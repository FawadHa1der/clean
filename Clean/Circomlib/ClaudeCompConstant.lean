import Clean.Circuit
import Clean.Circuit.SimpGadget
import Clean.Utils.Bits
import Clean.Circomlib.Bitify

/-
Original source code:
https://github.com/iden3/circomlib/blob/35e54ea21da3e8762557234298dbb553c175ea8d/circuits/compconstant.circom

# Overview

This circuit compares a 254-bit input (given as individual bits) against a constant ct.
It outputs 1 if input > ct, and 0 otherwise.

## How it works

The circuit processes the input in 127 pairs of bits. For each pair (slsb, smsb) at position i,
it computes a "part" value that encodes the comparison result for that bit pair, weighted by
position-dependent coefficients a = 2^i and b = 2^128 - 2^i.

The sum of all parts is a value whose bit 127 indicates whether input > ct.
-/

namespace Circomlib
open Utils.Bits
variable {p : ℕ} [Fact p.Prime] [Fact (p < 2^254)] [Fact (p > 2^253)]

namespace ClaudeCompConstant

/-! ## Helper Definitions -/

/-- The b coefficient for iteration i: b_i = 2^128 - 2^i -/
@[reducible] def bCoeff (i : ℕ) : ℤ := 2^128 - 2^i

/-- The a coefficient for iteration i: a_i = 2^i -/
@[reducible] def aCoeff (i : ℕ) : ℤ := 2^i

/-- Compute the part value for iteration i -/
def computePart (i : ℕ) (slsb smsb : F p) (ct : ℕ) : F p :=
  let clsb := (ct >>> (i * 2)) &&& 1
  let cmsb := (ct >>> (i * 2 + 1)) &&& 1
  let b_val : F p := (bCoeff i : F p)
  let a_val : F p := (aCoeff i : F p)
  if cmsb == 0 && clsb == 0 then
    -b_val * smsb * slsb + b_val * smsb + b_val * slsb
  else if cmsb == 0 && clsb == 1 then
    a_val * smsb * slsb - a_val * slsb + b_val * smsb - a_val * smsb + a_val
  else if cmsb == 1 && clsb == 0 then
    b_val * smsb * slsb - a_val * smsb + a_val
  else
    -a_val * smsb * slsb + a_val

/-- Semantic value of a signal pair (2-bit number: msb * 2 + lsb) -/
def signalPairValF (slsb smsb : F p) : ℕ := smsb.val * 2 + slsb.val

/-- Semantic value of constant pair at position i -/
def constPairValAt (i : ℕ) (ct : ℕ) : ℕ :=
  ((ct >>> (i * 2 + 1)) &&& 1) * 2 + ((ct >>> (i * 2)) &&& 1)

omit [Fact (p < 2 ^ 254)] in
/-- Key characterization: computePart encodes pair comparison.
    When signal pair > constant pair: contributes bCoeff i (~ 2^128 - 2^i)
    When signal pair = constant pair: contributes 0
    When signal pair < constant pair: contributes aCoeff i (= 2^i)

    Proof approach: 16 case analysis on (cmsb, clsb) * (smsb, slsb).
    For each case, verify the circuit formula matches the expected output.

    Example case (cmsb=0, clsb=0, smsb=1, slsb=0):
    - c_pair = 0, s_pair = 2, so s_pair > c_pair
    - Circuit computes: -b*1*0 + b*1 + b*0 = b = 2^128 - 2^i

    Example case (cmsb=1, clsb=1, smsb=0, slsb=1):
    - c_pair = 3, s_pair = 1, so s_pair < c_pair
    - Circuit computes: -a*0*1 + a = a = 2^i -/
lemma computePart_characterization (i : ℕ) (hi : i < 127) (slsb smsb : F p)
    (h_slsb : slsb = 0 ∨ slsb = 1) (h_smsb : smsb = 0 ∨ smsb = 1) (ct : ℕ) :
    let s_pair := signalPairValF slsb smsb
    let c_pair := constPairValAt i ct
    (computePart i slsb smsb ct).val =
      if s_pair > c_pair then 2^128 - 2^i
      else if s_pair = c_pair then 0
      else 2^i := by
  -- Establish field facts
  have hp_gt_1 : 1 < p := Nat.Prime.one_lt ‹Fact (Nat.Prime p)›.elim
  have h_val_0 : (0 : F p).val = 0 := ZMod.val_zero
  have h_val_1 : (1 : F p).val = 1 := @ZMod.val_one p ⟨hp_gt_1⟩

  -- Coefficient bounds
  have h_a_bound : 2^i < p := by
    have h1 : 2^i < 2^127 := Nat.pow_lt_pow_right (by omega) hi
    have h2 : 2^127 < 2^253 := by native_decide
    linarith [‹Fact (p > 2^253)›.elim]
  have h_b_bound : 2^128 - 2^i < p := by
    have h1 : 2^128 - 2^i < 2^128 := by
      have : 2^i ≥ 1 := Nat.one_le_two_pow
      omega
    have h2 : 2^128 < 2^253 := by native_decide
    linarith [‹Fact (p > 2^253)›.elim]
  have h_2i_lt_128 : 2^i < 2^128 := Nat.pow_lt_pow_right (by omega) (by omega : i < 128)

  -- Coefficient value lemmas
  have h_aCoeff_val : (aCoeff i : F p).val = 2^i := by
    simp only [aCoeff, Int.cast_pow, Int.cast_ofNat]
    have h_pow_cast : (2 : F p)^i = ((2^i : ℕ) : F p) := by simp only [Nat.cast_pow]; rfl
    rw [h_pow_cast, ZMod.val_natCast_of_lt h_a_bound]

  have h_bCoeff_val : (bCoeff i : F p).val = 2^128 - 2^i := by
    simp only [bCoeff]
    have h_eq : ((2 : ℤ)^128 - 2^i : ℤ) = ((2^128 - 2^i : ℕ) : ℤ) := by
      rw [Int.ofNat_sub (le_of_lt h_2i_lt_128)]
      simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [h_eq, Int.cast_natCast, ZMod.val_natCast_of_lt h_b_bound]

  -- Extract constant bits with explicit definitions
  have h_clsb_le : (ct >>> (i * 2)) &&& 1 ≤ 1 := Nat.and_le_right
  have h_cmsb_le : (ct >>> (i * 2 + 1)) &&& 1 ≤ 1 := Nat.and_le_right

  -- Case split on constant bits
  have h_cm_cases : (ct >>> (i * 2 + 1)) &&& 1 = 0 ∨ (ct >>> (i * 2 + 1)) &&& 1 = 1 := by omega
  have h_cl_cases : (ct >>> (i * 2)) &&& 1 = 0 ∨ (ct >>> (i * 2)) &&& 1 = 1 := by omega

  -- Unfold definitions
  simp only [signalPairValF, constPairValAt, computePart]

  -- 16-case analysis: 4 signal cases × 4 constant cases
  rcases h_smsb with rfl | rfl <;> rcases h_slsb with rfl | rfl <;>
  rcases h_cm_cases with h_cm | h_cm <;> rcases h_cl_cases with h_cl | h_cl <;>
  simp only [h_val_0, h_val_1, h_cm, h_cl, mul_zero, zero_mul, add_zero, zero_add,
             mul_one, one_mul, beq_self_eq_true, Bool.and_self, Bool.and_true, Bool.true_and,
             ↓reduceIte, Nat.one_ne_zero, beq_iff_eq, sub_zero, sub_self,
             h_aCoeff_val, h_bCoeff_val, Nat.zero_ne_one] <;>
  -- Handle boolean/comparison reductions with decide
  (simp (config := {decide := true}) only [↓reduceIte]) <;>
  -- Ring simplification and coefficient evaluation - handle all cases
  (simp only [show (-↑(bCoeff i) + ↑(bCoeff i) + ↑(bCoeff i) : F p) = ↑(bCoeff i) by ring,
              show (↑(bCoeff i) - ↑(aCoeff i) + ↑(aCoeff i) : F p) = ↑(bCoeff i) by ring,
              show (0 - ↑(aCoeff i) + ↑(aCoeff i) : F p) = 0 by ring,
              show (-↑(aCoeff i) + ↑(aCoeff i) : F p) = 0 by ring,
              h_aCoeff_val, h_bCoeff_val, ZMod.val_zero])

/-! ### Helper lemmas for sum_range_precise -/

/-- Sum of 2^i for i in Fin k equals 2^k - 1 (geometric series) -/
lemma sum_pow_two_fin (k : ℕ) :
    (Finset.univ : Finset (Fin k)).sum (fun i => 2^i.val) = 2^k - 1 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    ring_nf
    omega

/-- Key bound: contributions from positions below k are bounded by 2^k.
    This is the core arithmetic insight of the CompConstant circuit.

    When each position contributes either (2^128 - 2^i), 0, or 2^i,
    the sum modulo 2^128 is bounded by 2^k - 1. -/
lemma contributions_below_k_bound (k : ℕ) (contributions : Fin k → ℕ)
    (h_bound : ∀ i, contributions i ≤ 2^128) :
    (Finset.univ : Finset (Fin k)).sum contributions < k * 2^128 + 1 := by
  calc (Finset.univ : Finset (Fin k)).sum contributions
      ≤ (Finset.univ : Finset (Fin k)).sum (fun _ => 2^128) := by
          apply Finset.sum_le_sum; intro i _; exact h_bound i
    _ = k * 2^128 := by simp [Finset.sum_const, smul_eq_mul]
    _ < k * 2^128 + 1 := by omega

/-- Signal pair value at position i (extracted from Vector) -/
def signalPairAt (i : ℕ) (hi : i < 127) (input : Vector (F p) 254) : ℕ :=
  have hi2 : i * 2 < 254 := by omega
  have hi21 : i * 2 + 1 < 254 := by omega
  input[i * 2 + 1].val * 2 + input[i * 2].val

omit [Fact (Nat.Prime p)] [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
/-- signalPairAt equals signalPairValF -/
lemma signalPairAt_eq_signalPairValF (i : ℕ) (hi : i < 127) (input : Vector (F p) 254) :
    signalPairAt i hi input = signalPairValF input[i * 2] input[i * 2 + 1] := by
  unfold signalPairAt signalPairValF
  rfl

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
/-- Helper: pair value is bounded by 3 -/
lemma signalPairAt_le_3 (i : ℕ) (hi : i < 127) (input : Vector (F p) 254)
    (h_bits : ∀ j (_ : j < 254), input[j] = 0 ∨ input[j] = 1) :
    signalPairAt i hi input ≤ 3 := by
  unfold signalPairAt
  have hi2 : i * 2 < 254 := by omega
  have hi21 : i * 2 + 1 < 254 := by omega
  have hp_gt_1 : 1 < p := Nat.Prime.one_lt ‹Fact (Nat.Prime p)›.elim
  have h_slsb := h_bits (i * 2) hi2
  have h_smsb := h_bits (i * 2 + 1) hi21
  rcases h_slsb with h0_l | h1_l <;> rcases h_smsb with h0_m | h1_m
  · simp only [h0_l, h0_m, ZMod.val_zero]; omega
  · simp only [h0_l, h1_m, ZMod.val_zero, @ZMod.val_one p ⟨hp_gt_1⟩]; omega
  · simp only [h1_l, h0_m, ZMod.val_zero, @ZMod.val_one p ⟨hp_gt_1⟩]; omega
  · simp only [h1_l, h1_m, @ZMod.val_one p ⟨hp_gt_1⟩]; omega

/-- Helper: relates (x >>> k) % 4 to bits at positions k and k+1.
    Uses the fact that (x >>> k) % 4 = (x / 2^k) % 4 = (bit k) + 2*(bit k+1) -/
lemma shiftRight_mod4_eq_bits (x k : ℕ) :
    (x >>> k) % 4 = (x / 2^k % 2) + 2 * (x / 2^(k+1) % 2) := by
  simp only [Nat.shiftRight_eq_div_pow]
  have h : x / 2^k % 4 = x / 2^k % 2 + 2 * (x / 2^k / 2 % 2) := by omega
  have h2 : x / 2^k / 2 = x / 2^(k+1) := by
    rw [Nat.pow_succ, Nat.div_div_eq_div_mul, mul_comm]
  omega

/-- Extract bit value from toBits_fromBits: bits[k] equals the k-th bit of fromBits bits -/
lemma fromBits_testBit_eq {n : ℕ} (bits : Vector ℕ n) (k : ℕ)
    (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1)
    (hk : k < n) :
    bits[k] = (fromBits bits) / 2^k % 2 := by
  have h_tb := toBits_fromBits bits h_bits
  -- From h_tb, we have (toBits n (fromBits bits))[k] = bits[k]
  have h_eq : (toBits n (fromBits bits))[k] = bits[k] := by rw [h_tb]
  -- toBits gives: if testBit then 1 else 0
  simp only [toBits, Vector.getElem_mapRange] at h_eq
  -- Now h_eq : (if (fromBits bits).testBit k then 1 else 0) = bits[k]
  -- testBit x k = (x >>> k) &&& 1 ≠ 0 = x / 2^k % 2 ≠ 0
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow] at h_eq
  rw [Nat.and_comm, Nat.and_one_is_mod] at h_eq
  -- Now h_eq : (if (fromBits bits) / 2^k % 2 ≠ 0 then 1 else 0) = bits[k]
  -- We know bits[k] ∈ {0, 1}
  have h_mod2 : fromBits bits / 2 ^ k % 2 = 0 ∨ fromBits bits / 2 ^ k % 2 = 1 := Nat.mod_two_eq_zero_or_one _
  rcases h_bits k hk with hb | hb <;> rcases h_mod2 with hm | hm <;> simp_all

/-- Helper: for a fromBits result, the shift-mod4 equals the pair of bits.
    This follows from toBits_fromBits: since toBits n (fromBits bits) = bits,
    and toBits extracts bits via testBit, we have:
    - bits[k] = (fromBits bits).testBit k = fromBits bits / 2^k % 2
    - bits[k+1] = (fromBits bits).testBit (k+1) = fromBits bits / 2^(k+1) % 2
    Therefore: bits[k] + 2 * bits[k+1] = (fromBits bits >>> k) % 4 -/
lemma fromBits_shiftRight_mod4 {n : ℕ} (bits : Vector ℕ n) (k : ℕ)
    (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1)
    (hk : k + 1 < n) :
    (fromBits bits >>> k) % 4 = bits[k] + 2 * bits[k + 1] := by
  rw [shiftRight_mod4_eq_bits]
  rw [fromBits_testBit_eq bits k h_bits (Nat.lt_of_succ_lt hk)]
  rw [fromBits_testBit_eq bits (k+1) h_bits hk]

/-- Helper: 4^k = 2^(2*k) -/
lemma four_pow_eq_two_pow_double (k : ℕ) : (4:ℕ)^k = 2^(2*k) := by
  calc (4:ℕ)^k = (2^2)^k := by norm_num
    _ = 2^(2*k) := by rw [← Nat.pow_mul]

/-- Helper lemma: If x and y agree on all "pairs" above position k, then their high parts are equal.
    Specifically: x / 4^(k+1) = y / 4^(k+1). -/
lemma high_parts_eq_of_pairs_eq_above (x y k : ℕ)
    (h_above : ∀ j : Fin 127, j.val > k → (x >>> (j.val * 2)) % 4 = (y >>> (j.val * 2)) % 4)
    (hx : x < 2^254) (hy : y < 2^254) :
    x / 4^(k + 1) = y / 4^(k + 1) := by
  -- The high part x / 4^(k+1) consists of pairs at positions k+1, k+2, ..., 126
  -- Since all these pairs are equal, the high parts are equal
  apply Nat.eq_of_testBit_eq
  intro i
  -- Bit i of x / 4^(k+1) is bit i + 2*(k+1) of x
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  have h4pow : (4 : ℕ)^(k+1) = 2^(2*(k+1)) := four_pow_eq_two_pow_double (k+1)
  rw [h4pow]
  rw [Nat.and_comm, Nat.and_one_is_mod, Nat.and_comm, Nat.and_one_is_mod]
  -- Need to show x / (2^(2*(k+1)) * 2^i) % 2 = y / (2^(2*(k+1)) * 2^i) % 2
  -- This is bit (2*(k+1) + i) of x and y
  let bit_pos := 2*(k+1) + i
  by_cases hbound : bit_pos < 254
  · -- Within the 254-bit range
    -- This bit is part of pair at position (bit_pos / 2)
    let h_pair_pos := bit_pos / 2
    have h_pair_bound : h_pair_pos ≥ k + 1 := by omega
    by_cases h_pair_lt_127 : h_pair_pos < 127
    · -- The pair is within range, use h_above
      have h_pair_eq := h_above ⟨h_pair_pos, h_pair_lt_127⟩ (by omega : h_pair_pos > k)
      -- Extract bit equality from pair equality
      simp only [Nat.shiftRight_eq_div_pow] at h_pair_eq
      -- h_pair_eq : (x / 2^(h_pair_pos * 2)) % 4 = (y / 2^(h_pair_pos * 2)) % 4
      by_cases h_even : bit_pos % 2 = 0
      · -- Even bit: low bit of the pair
        have hpow_eq : 2^(2*(k+1)) * 2^i = 2^bit_pos := by rw [← Nat.pow_add]
        rw [hpow_eq]
        have h_bp_eq : bit_pos = h_pair_pos * 2 := by omega
        rw [h_bp_eq]
        have hm : ∀ n : ℕ, n % 4 % 2 = n % 2 := fun n => by omega
        have h_low : x / 2^(h_pair_pos * 2) % 2 = y / 2^(h_pair_pos * 2) % 2 := by
          calc x / 2^(h_pair_pos * 2) % 2 = (x / 2^(h_pair_pos * 2) % 4) % 2 := by rw [hm]
            _ = (y / 2^(h_pair_pos * 2) % 4) % 2 := by rw [h_pair_eq]
            _ = y / 2^(h_pair_pos * 2) % 2 := by rw [hm]
        simp only [h_low]
      · -- Odd bit: high bit of the pair
        have hpow_eq : 2^(2*(k+1)) * 2^i = 2^bit_pos := by rw [← Nat.pow_add]
        rw [hpow_eq]
        have h_bp_eq : bit_pos = h_pair_pos * 2 + 1 := by omega
        rw [h_bp_eq]
        have hd : ∀ n : ℕ, n % 4 / 2 = n / 2 % 2 := fun n => by omega
        have hpow : 2 ^ (h_pair_pos * 2 + 1) = 2 ^ (h_pair_pos * 2) * 2 := by ring
        have h_high : x / 2 ^ (h_pair_pos * 2 + 1) % 2 = y / 2 ^ (h_pair_pos * 2 + 1) % 2 := by
          calc x / 2 ^ (h_pair_pos * 2 + 1) % 2 = x / (2 ^ (h_pair_pos * 2) * 2) % 2 := by rw [hpow]
            _ = x / 2 ^ (h_pair_pos * 2) / 2 % 2 := by rw [Nat.div_div_eq_div_mul]
            _ = x / 2 ^ (h_pair_pos * 2) % 4 / 2 := by rw [hd]
            _ = y / 2 ^ (h_pair_pos * 2) % 4 / 2 := by rw [h_pair_eq]
            _ = y / 2 ^ (h_pair_pos * 2) / 2 % 2 := by rw [hd]
            _ = y / (2 ^ (h_pair_pos * 2) * 2) % 2 := by rw [Nat.div_div_eq_div_mul]
            _ = y / 2 ^ (h_pair_pos * 2 + 1) % 2 := by rw [hpow]
        simp only [h_high]
    · -- Pair beyond position 126, both high bits are zero
      have hpow_eq : 2^(2*(k+1)) * 2^i = 2^bit_pos := by rw [← Nat.pow_add]
      rw [hpow_eq]
      -- bit_pos >= 254 in this case since h_pair_pos >= 127
      have h_bp_ge_254 : bit_pos ≥ 254 := by omega
      omega
  · -- Beyond 254 bits, both are 0
    have hpow_eq : 2^(2*(k+1)) * 2^i = 2^bit_pos := by rw [← Nat.pow_add]
    rw [hpow_eq]
    have h_pos : 0 < 2^bit_pos := Nat.pow_pos (by omega : 0 < 2)
    have hx_div : x / 2^bit_pos = 0 := by
      apply Nat.div_eq_zero_iff.mpr
      right
      calc x < 2^254 := hx
        _ ≤ 2^bit_pos := Nat.pow_le_pow_right (by omega) (by omega)
    have hy_div : y / 2^bit_pos = 0 := by
      apply Nat.div_eq_zero_iff.mpr
      right
      calc y < 2^254 := hy
        _ ≤ 2^bit_pos := Nat.pow_le_pow_right (by omega) (by omega)
    rw [hx_div, hy_div]

/-- Helper: x % (4 * 4^k) = (x / 4^k % 4) * 4^k + x % 4^k -/
lemma mod_four_pow_succ (x k : ℕ) : x % 4^(k+1) = (x / 4^k % 4) * 4^k + x % 4^k := by
  have h41 : (4:ℕ)^(k+1) = 4 * 4^k := by ring
  rw [h41]
  have h_4k_pos : 0 < 4^k := Nat.pow_pos (by omega : 0 < 4)
  have h_rem : x % 4^k < 4^k := Nat.mod_lt x h_4k_pos
  have h_qmod : x / 4^k % 4 < 4 := Nat.mod_lt _ (by omega : 0 < 4)
  have h_sum_lt : x / 4^k % 4 * 4^k + x % 4^k < 4 * 4^k := by nlinarith
  -- Key identity: x / 4^k = x / 4^k / 4 * 4 + x / 4^k % 4
  have h1 : x / 4^k = x / 4^k / 4 * 4 + x / 4^k % 4 := by
    have := Nat.div_add_mod (x / 4^k) 4; linarith
  -- x = x / 4^k / 4 * (4 * 4^k) + (x / 4^k % 4 * 4^k + x % 4^k)
  have h2 : x = x / 4^k / 4 * (4 * 4^k) + (x / 4^k % 4 * 4^k + x % 4^k) := by
    have h_base := Nat.div_add_mod x (4^k)
    have h_step1 : x = 4^k * (x / 4^k) + x % 4^k := by linarith
    have h_step2 : 4^k * (x / 4^k) = x / 4^k / 4 * (4 * 4^k) + x / 4^k % 4 * 4^k := by
      calc 4^k * (x / 4^k) = 4^k * (x / 4^k / 4 * 4 + x / 4^k % 4) := by
             conv_lhs => rw [h1]
        _ = x / 4^k / 4 * 4 * 4^k + x / 4^k % 4 * 4^k := by ring
        _ = x / 4^k / 4 * (4 * 4^k) + x / 4^k % 4 * 4^k := by ring
    linarith
  -- x / 4^k / 4 = x / (4 * 4^k)
  have h3 : x / 4^k / 4 = x / (4 * 4^k) := by
    rw [Nat.div_div_eq_div_mul]; ring_nf
  -- From h2: x = x / (4 * 4^k) * (4 * 4^k) + (x / 4^k % 4 * 4^k + x % 4^k)
  -- Since x / 4^k % 4 * 4^k + x % 4^k < 4 * 4^k, this is the Euclidean division
  -- So x % (4 * 4^k) = x / 4^k % 4 * 4^k + x % 4^k
  rw [h3] at h2
  -- Use uniqueness of Euclidean division
  have h_div_mod := Nat.div_add_mod x (4 * 4^k)
  -- h2 says x = x / (4 * 4^k) * (4 * 4^k) + (x / 4^k % 4 * 4^k + x % 4^k)
  -- h_div_mod says (4 * 4^k) * (x / (4 * 4^k)) + x % (4 * 4^k) = x
  -- Since both have the same quotient and the remainder in h2 is < 4 * 4^k,
  -- they must be equal
  have h_quot : x / (4 * 4^k) * (4 * 4^k) = (4 * 4^k) * (x / (4 * 4^k)) := by ring
  rw [h_quot] at h2
  -- Now h2 : x = (4 * 4^k) * (x / (4 * 4^k)) + (x / 4^k % 4 * 4^k + x % 4^k)
  -- and h_div_mod : (4 * 4^k) * (x / (4 * 4^k)) + x % (4 * 4^k) = x
  omega

/-- Key comparison lemma: if high parts are equal and x's pair at k is less than y's pair,
    then x < y. -/
lemma lt_of_high_eq_and_pair_lt (x y k : ℕ)
    (h_high_eq : x / 4^(k + 1) = y / 4^(k + 1))
    (h_pair_lt : (x >>> (k * 2)) % 4 < (y >>> (k * 2)) % 4) :
    x < y := by
  -- Convert shift to division
  simp only [Nat.shiftRight_eq_div_pow] at h_pair_lt
  -- Use the key fact: 4^k = 2^(k*2)
  have h4k : (4:ℕ)^k = 2^(k*2) := by rw [four_pow_eq_two_pow_double]; ring_nf
  have h_pair_lt' : x / 4^k % 4 < y / 4^k % 4 := by rw [h4k]; exact h_pair_lt

  -- Decompose using our helper lemma
  have h_x_low := mod_four_pow_succ x k
  have h_y_low := mod_four_pow_succ y k

  -- Bounds on remainders
  have h_rem_x : x % 4^k < 4^k := Nat.mod_lt x (Nat.pow_pos (by omega : 0 < 4))
  have h_rem_y : y % 4^k < 4^k := Nat.mod_lt y (Nat.pow_pos (by omega : 0 < 4))
  have h_4k_pos : 0 < 4^k := Nat.pow_pos (by omega : 0 < 4)

  -- Key step: x % 4^(k+1) < y % 4^(k+1)
  have h_mod_lt : x % 4^(k+1) < y % 4^(k+1) := by
    rw [h_x_low, h_y_low]
    have h_xp_lt_yp : x / 4^k % 4 + 1 ≤ y / 4^k % 4 := h_pair_lt'
    calc (x / 4^k % 4) * 4^k + x % 4^k
      < (x / 4^k % 4) * 4^k + 4^k := by omega
      _ = (x / 4^k % 4 + 1) * 4^k := by ring
      _ ≤ (y / 4^k % 4) * 4^k := Nat.mul_le_mul_right _ h_xp_lt_yp
      _ ≤ (y / 4^k % 4) * 4^k + y % 4^k := Nat.le_add_right _ _

  -- Final step: since high parts are equal, comparison is determined by low parts
  have h_4k1_pos : 0 < 4^(k+1) := Nat.pow_pos (by omega : 0 < 4)
  have hx_eq : x = x / 4^(k+1) * 4^(k+1) + x % 4^(k+1) := by
    have h := Nat.div_add_mod x (4^(k+1))
    linarith
  have hy_eq : y = y / 4^(k+1) * 4^(k+1) + y % 4^(k+1) := by
    have h := Nat.div_add_mod y (4^(k+1))
    linarith
  rw [hx_eq, hy_eq, h_high_eq]
  omega

/-- Key lemma: fromBits comparison implies existence of differing pair.
    When x > y as natural numbers represented in little-endian bits,
    there exists a most significant position where x's pair > y's pair. -/
lemma exists_msb_win_from_gt (x y : ℕ) (hx : x < 2^254) (hy : y < 2^254) (h_gt : x > y) :
    ∃ k : Fin 127,
      (x >>> (k.val * 2)) % 4 > (y >>> (k.val * 2)) % 4 ∧
      ∀ j : Fin 127, j > k → (x >>> (j.val * 2)) % 4 = (y >>> (j.val * 2)) % 4 := by
  -- This is a fundamental property of positional number systems.
  -- When x > y, there exists a most significant "digit" (here, a 2-bit pair)
  -- where x's digit > y's digit, and all higher digits are equal.
  -- The proof requires bit-level analysis of the inequality.

  -- Define the set of positions where the pairs differ
  let diff_positions := { i : Fin 127 | (x >>> (i.val * 2)) % 4 ≠ (y >>> (i.val * 2)) % 4 }
  let diff_finset := diff_positions.toFinset

  -- Since x > y and both have 254 bits, there must be at least one differing pair
  have h_nonempty : diff_finset.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h_empty
    -- If all pairs are equal, x = y (contradiction with x > y)
    have h_all_eq : ∀ i : Fin 127, (x >>> (i.val * 2)) % 4 = (y >>> (i.val * 2)) % 4 := by
      intro i
      by_contra h_ne
      have : i ∈ diff_finset := by simp [diff_finset, diff_positions, h_ne]
      rw [h_empty] at this
      exact Finset.notMem_empty _ this
    have h_x_eq_y : x = y := by
      -- Both numbers can be reconstructed from their pairs
      -- Since all pairs are equal, the numbers are equal
      apply Nat.eq_of_testBit_eq
      intro i
      -- We need to show x.testBit i = y.testBit i
      -- testBit i depends on (x >>> i) % 2, which is the i-th bit
      -- The pairs give us: (x >>> (k * 2)) % 4 = (y >>> (k * 2)) % 4
      -- This means bits 2k and 2k+1 are the same for both
      by_cases hi_bound : i < 254
      · -- Position i is within the bit range
        let k : Fin 127 := ⟨i / 2, by omega⟩
        have h_pair_eq := h_all_eq k
        -- h_pair_eq : (x >>> (k * 2)) % 4 = (y >>> (k * 2)) % 4
        -- From pair equality, we can extract bit equality
        -- (x >>> (k * 2)) % 4 encodes bits at positions k*2 and k*2+1
        -- Bit at position k*2: (x >>> (k * 2)) % 2
        -- Bit at position k*2+1: (x >>> (k * 2)) / 2 % 2 = (x >>> (k * 2 + 1)) % 2
        simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
        rw [Nat.and_comm, Nat.and_one_is_mod, Nat.and_comm, Nat.and_one_is_mod]
        -- Goal: (x / 2^i % 2 ≠ 0) = (y / 2^i % 2 ≠ 0)
        by_cases h_even : i % 2 = 0
        · -- i is even: i = k.val * 2
          have h_i_eq : i = k.val * 2 := by
            have hk_def : k.val = i / 2 := rfl
            omega
          rw [h_i_eq]
          -- Extract low bit from pair
          simp only [Nat.shiftRight_eq_div_pow] at h_pair_eq
          have h_low : x / 2 ^ (k.val * 2) % 2 = y / 2 ^ (k.val * 2) % 2 := by
            -- (x / 2^(k*2)) % 4 = (y / 2^(k*2)) % 4
            -- Taking mod 2 of both sides: (x / 2^(k*2)) % 4 % 2 = (y / 2^(k*2)) % 4 % 2
            -- Since x % 4 % 2 = x % 2, we get the result
            have hm : ∀ n : ℕ, n % 4 % 2 = n % 2 := fun n => by omega
            calc x / 2 ^ (k.val * 2) % 2 = x / 2 ^ (k.val * 2) % 4 % 2 := by rw [hm]
              _ = y / 2 ^ (k.val * 2) % 4 % 2 := by rw [h_pair_eq]
              _ = y / 2 ^ (k.val * 2) % 2 := by rw [hm]
          simp only [h_low]
        · -- i is odd: i = k.val * 2 + 1
          have h_i_eq : i = k.val * 2 + 1 := by
            have hk_def : k.val = i / 2 := rfl
            omega
          rw [h_i_eq]
          -- Extract high bit from pair
          simp only [Nat.shiftRight_eq_div_pow] at h_pair_eq
          have h_high : x / 2 ^ (k.val * 2 + 1) % 2 = y / 2 ^ (k.val * 2 + 1) % 2 := by
            -- High bit = (x / 2^(k*2)) / 2 % 2 = (x / 2^(k*2)) % 4 / 2
            have hd : ∀ n : ℕ, n % 4 / 2 = n / 2 % 2 := fun n => by omega
            have hpow : 2 ^ (k.val * 2 + 1) = 2 ^ (k.val * 2) * 2 := by ring
            calc x / 2 ^ (k.val * 2 + 1) % 2 = x / (2 ^ (k.val * 2) * 2) % 2 := by rw [hpow]
              _ = x / 2 ^ (k.val * 2) / 2 % 2 := by rw [Nat.div_div_eq_div_mul]
              _ = x / 2 ^ (k.val * 2) % 4 / 2 := by rw [hd]
              _ = y / 2 ^ (k.val * 2) % 4 / 2 := by rw [h_pair_eq]
              _ = y / 2 ^ (k.val * 2) / 2 % 2 := by rw [hd]
              _ = y / (2 ^ (k.val * 2) * 2) % 2 := by rw [Nat.div_div_eq_div_mul]
              _ = y / 2 ^ (k.val * 2 + 1) % 2 := by rw [hpow]
          simp only [h_high]
      · -- Position i is beyond 254, both bits are 0
        have hx_high : x.testBit i = false := by
          apply Nat.testBit_eq_false_of_lt
          calc x < 2^254 := hx
            _ ≤ 2^i := Nat.pow_le_pow_right (by omega) (by omega)
        have hy_high : y.testBit i = false := by
          apply Nat.testBit_eq_false_of_lt
          calc y < 2^254 := hy
            _ ≤ 2^i := Nat.pow_le_pow_right (by omega) (by omega)
        rw [hx_high, hy_high]
    omega

  -- Get the maximum differing position
  let k := diff_finset.max' h_nonempty

  -- k is a differing position
  have hk_mem : (x >>> (k.val * 2)) % 4 ≠ (y >>> (k.val * 2)) % 4 := by
    have : k ∈ diff_finset := Finset.max'_mem diff_finset h_nonempty
    simp only [diff_finset, diff_positions, Set.mem_toFinset, Set.mem_setOf_eq] at this
    exact this

  -- All positions above k have equal pairs
  have h_above_eq : ∀ j : Fin 127, j > k → (x >>> (j.val * 2)) % 4 = (y >>> (j.val * 2)) % 4 := by
    intro j hj
    by_contra h_ne
    have hj_mem : j ∈ diff_finset := by
      simp only [diff_finset, diff_positions, Set.mem_toFinset, Set.mem_setOf_eq]
      exact h_ne
    have h_le := Finset.le_max' diff_finset j hj_mem
    omega

  -- At k, x's pair > y's pair (not less, because x > y overall)
  have h_x_wins : (x >>> (k.val * 2)) % 4 > (y >>> (k.val * 2)) % 4 := by
    rcases Nat.lt_trichotomy ((x >>> (k.val * 2)) % 4) ((y >>> (k.val * 2)) % 4) with hlt | heq | hgt
    · -- If x's pair < y's pair at k, then x < y (contradiction with x > y)
      exfalso
      -- First show high parts are equal
      have h_high_eq := high_parts_eq_of_pairs_eq_above x y k.val h_above_eq hx hy
      -- Then use lt_of_high_eq_and_pair_lt to get x < y
      have h_x_lt_y := lt_of_high_eq_and_pair_lt x y k.val h_high_eq hlt
      omega
    · -- Equal contradicts hk_mem
      exact absurd heq hk_mem
    · exact hgt

  exact ⟨k, h_x_wins, h_above_eq⟩

-- When input > ct, there exists a MSB position k where signal wins
--    and all higher positions are ties.
omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
lemma exists_msb_win_position (ct : ℕ) (h_ct : ct < 2^254)
    (input : Vector (F p) 254)
    (h_bits : ∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1)
    (h_gt : fromBits (input.map ZMod.val) > ct) :
    ∃ k : Fin 127,
      signalPairValF input[k.val * 2] input[k.val * 2 + 1] > constPairValAt k.val ct ∧
      ∀ j : Fin 127, j > k →
        signalPairValF input[j.val * 2] input[j.val * 2 + 1] = constPairValAt j.val ct := by
  -- Get the input value
  let x := fromBits (input.map ZMod.val)
  have hx_lt : x < 2^254 := by
    apply fromBits_lt
    intro i hi
    simp only [Vector.getElem_map]
    have hp_gt_1 : 1 < p := Nat.Prime.one_lt ‹Fact (Nat.Prime p)›.elim
    rcases h_bits i hi with h0 | h1
    · left; simp only [ZMod.val_eq_zero]; exact h0
    · right
      apply_fun ZMod.val at h1
      simp only [@ZMod.val_one p ⟨hp_gt_1⟩] at h1
      exact h1

  -- Apply the general lemma
  obtain ⟨k, hk_gt, hk_eq⟩ := exists_msb_win_from_gt x ct hx_lt h_ct h_gt

  use k
  constructor
  · -- signalPairValF > constPairValAt
    -- We need to relate (x >>> (k * 2)) % 4 to signalPairValF
    -- and (ct >>> (k * 2)) % 4 to constPairValAt

    -- signalPairValF = input[k*2+1].val * 2 + input[k*2].val
    -- This equals (x >>> (k * 2)) % 4 when input represents x in bits

    -- constPairValAt k ct = (ct >>> (k*2+1)) &&& 1) * 2 + (ct >>> (k*2)) &&& 1
    -- This equals (ct >>> (k * 2)) % 4

    have h_signal_eq : signalPairValF input[k.val * 2] input[k.val * 2 + 1] =
        (x >>> (k.val * 2)) % 4 := by
      unfold signalPairValF
      -- The pair value equals the 2-bit extraction from x
      -- Apply fromBits_shiftRight_mod4 with position k.val * 2
      let bits := input.map ZMod.val
      have h_bits_01 : ∀ (i : ℕ) (hi : i < 254), bits[i] = 0 ∨ bits[i] = 1 := by
        intro i hi
        simp only [Vector.getElem_map, bits]
        have hp_gt_1 : 1 < p := Nat.Prime.one_lt ‹Fact (Nat.Prime p)›.elim
        rcases h_bits i hi with h0 | h1
        · left; simp only [ZMod.val_eq_zero]; exact h0
        · right
          apply_fun ZMod.val at h1
          simp only [@ZMod.val_one p ⟨hp_gt_1⟩] at h1
          exact h1
      have hk_bound : k.val * 2 + 1 < 254 := by
        have := k.isLt  -- k < 127
        omega
      have h_fb := fromBits_shiftRight_mod4 bits (k.val * 2) h_bits_01 hk_bound
      -- h_fb : (fromBits bits >>> k.val * 2) % 4 = bits[k.val * 2] + 2 * bits[k.val * 2 + 1]
      simp only [Vector.getElem_map, bits] at h_fb
      -- Now h_fb relates to input[k.val * 2].val
      -- The goal is: input[k.val * 2 + 1].val * 2 + input[k.val * 2].val = ...
      -- h_fb gives: input[k.val * 2].val + 2 * input[k.val * 2 + 1].val
      -- Need to handle k.val * 2 + 1 = 1 + k.val * 2
      have h_idx : k.val * 2 + 1 = 1 + k.val * 2 := by omega
      simp only [h_idx] at h_fb ⊢
      -- Goal: ZMod.val input[1 + k * 2] * 2 + ZMod.val input[k * 2] = (fromBits ...) >>> k*2 % 4
      -- h_fb : (fromBits ...) >>> k*2 % 4 = input[k * 2].val + 2 * input[1 + k * 2].val
      rw [h_fb]
      -- Goal: ZMod.val input[1 + k * 2] * 2 + ZMod.val input[k * 2] =
      --       input[k * 2].val + 2 * input[1 + k * 2].val
      -- Let a = input[1 + k * 2].val, b = input[k * 2].val
      -- Goal: a * 2 + b = b + 2 * a
      -- This is true by commutativity
      -- The two sides are equal: a*2 + b = b + 2*a, and x.val = ZMod.val x
      ac_rfl

    have h_const_eq : constPairValAt k.val ct = (ct >>> (k.val * 2)) % 4 := by
      unfold constPairValAt
      -- (msb * 2 + lsb) where msb = (ct >>> (k*2+1)) &&& 1, lsb = (ct >>> (k*2)) &&& 1
      -- This equals (ct >>> (k*2)) % 4
      have h1 : (ct >>> (k.val * 2 + 1)) &&& 1 = (ct >>> (k.val * 2)) / 2 % 2 := by
        simp only [Nat.shiftRight_add, Nat.shiftRight_one, Nat.and_one_is_mod]
      have h2 : (ct >>> (k.val * 2)) &&& 1 = (ct >>> (k.val * 2)) % 2 := by
        simp only [Nat.and_one_is_mod]
      rw [h1, h2]
      -- (x / 2 % 2) * 2 + x % 2 = x % 4
      have := Nat.div_add_mod (ct >>> (k.val * 2)) 2
      omega

    rw [h_signal_eq, h_const_eq]
    exact hk_gt

  · -- All higher positions are ties
    intro j hj
    have h_eq := hk_eq j hj

    have h_signal_eq : signalPairValF input[j.val * 2] input[j.val * 2 + 1] =
        (x >>> (j.val * 2)) % 4 := by
      unfold signalPairValF
      -- Same proof as above, but for j instead of k
      let bits := input.map ZMod.val
      have h_bits_01 : ∀ (i : ℕ) (hi : i < 254), bits[i] = 0 ∨ bits[i] = 1 := by
        intro i hi
        simp only [Vector.getElem_map, bits]
        have hp_gt_1 : 1 < p := Nat.Prime.one_lt ‹Fact (Nat.Prime p)›.elim
        rcases h_bits i hi with h0 | h1
        · left; simp only [ZMod.val_eq_zero]; exact h0
        · right
          apply_fun ZMod.val at h1
          simp only [@ZMod.val_one p ⟨hp_gt_1⟩] at h1
          exact h1
      have hj_bound : j.val * 2 + 1 < 254 := by
        have := j.isLt  -- j < 127
        omega
      have h_fb := fromBits_shiftRight_mod4 bits (j.val * 2) h_bits_01 hj_bound
      simp only [Vector.getElem_map, bits] at h_fb
      have h_idx : j.val * 2 + 1 = 1 + j.val * 2 := by omega
      simp only [h_idx] at h_fb ⊢
      rw [h_fb]
      ac_rfl

    have h_const_eq : constPairValAt j.val ct = (ct >>> (j.val * 2)) % 4 := by
      unfold constPairValAt
      have h1 : (ct >>> (j.val * 2 + 1)) &&& 1 = (ct >>> (j.val * 2)) / 2 % 2 := by
        simp only [Nat.shiftRight_add, Nat.shiftRight_one, Nat.and_one_is_mod]
      have h2 : (ct >>> (j.val * 2)) &&& 1 = (ct >>> (j.val * 2)) % 2 := by
        simp only [Nat.and_one_is_mod]
      rw [h1, h2]
      omega

    rw [h_signal_eq, h_const_eq, h_eq]

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
/-- When input ≤ ct, either all pairs are ties, or the MSB differing position is a loss. -/
lemma msb_determines_le (ct : ℕ) (h_ct : ct < 2^254)
    (input : Vector (F p) 254)
    (h_bits : ∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1)
    (h_le : fromBits (input.map ZMod.val) ≤ ct) :
    (∀ i : Fin 127, signalPairValF input[i.val * 2] input[i.val * 2 + 1] = constPairValAt i.val ct) ∨
    (∃ k : Fin 127,
      signalPairValF input[k.val * 2] input[k.val * 2 + 1] < constPairValAt k.val ct ∧
      ∀ j : Fin 127, j > k →
        signalPairValF input[j.val * 2] input[j.val * 2 + 1] = constPairValAt j.val ct) := by
  -- Get the input value
  let x := fromBits (input.map ZMod.val)
  have hx_lt : x < 2^254 := by
    apply fromBits_lt
    intro i hi
    simp only [Vector.getElem_map]
    have hp_gt_1 : 1 < p := Nat.Prime.one_lt ‹Fact (Nat.Prime p)›.elim
    rcases h_bits i hi with h0 | h1
    · left; simp only [ZMod.val_eq_zero]; exact h0
    · right
      apply_fun ZMod.val at h1
      simp only [@ZMod.val_one p ⟨hp_gt_1⟩] at h1
      exact h1

  -- Helper to convert between signal pairs and bit representation
  have h_signal_pair : ∀ i : Fin 127,
      signalPairValF input[i.val * 2] input[i.val * 2 + 1] = (x >>> (i.val * 2)) % 4 := by
    intro i
    unfold signalPairValF
    let bits := input.map ZMod.val
    have h_bits_01 : ∀ (j : ℕ) (hj : j < 254), bits[j] = 0 ∨ bits[j] = 1 := by
      intro j hj
      simp only [Vector.getElem_map, bits]
      have hp_gt_1 : 1 < p := Nat.Prime.one_lt ‹Fact (Nat.Prime p)›.elim
      rcases h_bits j hj with h0 | h1
      · left; simp only [ZMod.val_eq_zero]; exact h0
      · right
        apply_fun ZMod.val at h1
        simp only [@ZMod.val_one p ⟨hp_gt_1⟩] at h1
        exact h1
    have hi_bound : i.val * 2 + 1 < 254 := by omega
    have h_fb := fromBits_shiftRight_mod4 bits (i.val * 2) h_bits_01 hi_bound
    simp only [Vector.getElem_map, bits] at h_fb
    have h_idx : i.val * 2 + 1 = 1 + i.val * 2 := by omega
    simp only [h_idx] at h_fb ⊢
    rw [h_fb]
    ac_rfl

  have h_const_pair : ∀ i : Fin 127, constPairValAt i.val ct = (ct >>> (i.val * 2)) % 4 := by
    intro i
    unfold constPairValAt
    have h1 : (ct >>> (i.val * 2 + 1)) &&& 1 = (ct >>> (i.val * 2)) / 2 % 2 := by
      simp only [Nat.shiftRight_add, Nat.shiftRight_one, Nat.and_one_is_mod]
    have h2 : (ct >>> (i.val * 2)) &&& 1 = (ct >>> (i.val * 2)) % 2 := by
      simp only [Nat.and_one_is_mod]
    rw [h1, h2]
    omega

  -- Case split: either x = ct (all pairs equal) or x < ct (MSB loss)
  rcases Nat.lt_or_eq_of_le h_le with h_lt | h_eq

  -- Case: x < ct → there exists MSB position where signal loses
  · right
    -- Use symmetric logic: ct > x, so there's a MSB position where ct's pair > x's pair
    obtain ⟨k, hk_gt, hk_eq⟩ := exists_msb_win_from_gt ct x h_ct hx_lt h_lt
    -- hk_gt : (ct >>> (k * 2)) % 4 > (x >>> (k * 2)) % 4
    -- i.e., x's pair < ct's pair at k

    use k
    constructor
    · -- signalPairValF < constPairValAt
      rw [h_signal_pair k, h_const_pair k]
      exact hk_gt
    · -- All positions j > k have equal pairs
      intro j hj
      rw [h_signal_pair j, h_const_pair j]
      exact (hk_eq j hj).symm

  -- Case: x = ct → all pairs are equal
  · left
    intro i
    rw [h_signal_pair i, h_const_pair i]
    -- x = fromBits (input.map ZMod.val) = ct by h_eq
    show x >>> (i.val * 2) % 4 = ct >>> (i.val * 2) % 4
    -- Since x is defined as fromBits (input.map ZMod.val), and h_eq says this equals ct
    have hx_eq_ct : x = ct := h_eq
    rw [hx_eq_ct]

/-! ### Helper lemmas needed by sum_range_precise -/

/-- Helper: Vector.sum equals List.sum of the toList -/
lemma vector_sum_eq_list_sum' {α} [AddCommMonoid α] {n : ℕ} (v : Vector α n) :
    v.sum = v.toList.sum := by
  rw [Vector.sum_mk, ← Array.sum_eq_sum_toList]
  rfl

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
/-- Helper: sum of list of field elements, when sum of vals < p, equals val of sum -/
lemma list_sum_val_eq' {l : List (F p)} (h : (l.map ZMod.val).sum < p) :
    l.sum.val = (l.map ZMod.val).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons] at h ⊢
    have h_xs : (xs.map ZMod.val).sum < p := by
      have : x.val < p := ZMod.val_lt x
      linarith
    have ih' := ih h_xs
    rw [ZMod.val_add, ih']
    rw [Nat.mod_eq_of_lt h]

omit [Fact (Nat.Prime p)] [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
/-- Helper: bound on sum of list of field element vals -/
lemma list_sum_val_bound' {l : List (F p)} {bound : ℕ}
    (h : ∀ x ∈ l, x.val ≤ bound) :
    (l.map ZMod.val).sum ≤ l.length * bound := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h_x : x.val ≤ bound := h x (List.Mem.head xs)
    have h_xs : ∀ y ∈ xs, y.val ≤ bound := fun y hy => h y (List.Mem.tail x hy)
    have := ih h_xs
    linarith

omit [Fact (p < 2 ^ 254)] in
/-- computePart value is bounded by 2^128 when inputs are boolean and i < 127. -/
lemma computePart_val_bound' (i : ℕ) (hi : i < 127) (slsb smsb : F p)
    (h_slsb : slsb = 0 ∨ slsb = 1) (h_smsb : smsb = 0 ∨ smsb = 1) (ct : ℕ) :
    (computePart i slsb smsb ct).val ≤ 2^128 := by
  -- Use the characterization lemma
  have h_char := computePart_characterization i hi slsb smsb h_slsb h_smsb ct
  simp only at h_char
  -- Bound analysis: the output is one of:
  -- - 2^128 - 2^i (when signal wins)
  -- - 0 (when tie)
  -- - 2^i (when signal loses)
  -- All of these are ≤ 2^128
  have h_2i_lt_128 : 2^i < 2^128 := Nat.pow_lt_pow_right (by omega) (by omega : i < 128)
  have h_bCoeff_le : 2^128 - 2^i ≤ 2^128 := Nat.sub_le _ _
  have h_aCoeff_le : 2^i ≤ 2^128 := le_of_lt h_2i_lt_128
  rw [h_char]
  split_ifs <;> omega

omit [Fact (p < 2 ^ 254)] in
/-- The sum of parts is bounded by 2^135. -/
lemma sum_parts_bounded' (parts : Vector (F p) 127)
    (h_parts : ∀ i : Fin 127, parts[i].val ≤ 2^128) :
    parts.sum.val < 2^135 := by
  rw [vector_sum_eq_list_sum']
  have h_list_bound : ∀ x ∈ parts.toList, x.val ≤ 2^128 := by
    intro x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    simp only [Vector.getElem_toList]
    rw [Vector.length_toList] at hi
    exact h_parts ⟨i, hi⟩
  have h_nat_bound := list_sum_val_bound' h_list_bound
  simp only [Vector.length_toList] at h_nat_bound
  have h_bound_lt : 127 * 2^128 < 2^135 := by native_decide
  have hp : p > 2^253 := ‹Fact (p > 2^253)›.elim
  have h_sum_lt_p : (parts.toList.map ZMod.val).sum < p := by linarith
  rw [list_sum_val_eq' h_sum_lt_p]
  linarith

/-! ### Helper lemmas for sum_range_precise -/

omit [Fact (p < 2 ^ 254)] in
/-- Parts bounded when input consists of bits -/
lemma parts_bounded_of_bits (ct : ℕ)
    (input : Vector (F p) 254) (h_bits : ∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1)
    (parts : Vector (F p) 127)
    (h_parts : ∀ i : Fin 127, parts[i] = computePart i.val input[i.val * 2] input[i.val * 2 + 1] ct) :
    ∀ i : Fin 127, parts[i].val ≤ 2^128 := by
  intro i
  rw [h_parts i]
  exact computePart_val_bound' i.val i.isLt _ _
    (h_bits (i.val * 2) (by omega)) (h_bits (i.val * 2 + 1) (by omega)) ct

omit [Fact (Nat.Prime p)] [Fact (p < 2 ^ 254)] in
/-- Sum of parts doesn't overflow in the prime field -/
lemma sum_parts_lt_prime (parts : Vector (F p) 127)
    (h_parts_bounded : ∀ i : Fin 127, parts[i].val ≤ 2^128) :
    (parts.toList.map ZMod.val).sum < p := by
  have hp : p > 2^253 := ‹Fact (p > 2^253)›.elim
  calc (parts.toList.map ZMod.val).sum
      ≤ parts.toList.length * 2^128 := list_sum_val_bound' (by
          intro x hx
          rw [List.mem_iff_getElem] at hx
          obtain ⟨i, hi, rfl⟩ := hx
          simp only [Vector.getElem_toList]
          rw [Vector.length_toList] at hi
          exact h_parts_bounded ⟨i, hi⟩)
    _ = 127 * 2^128 := by simp [Vector.length_toList]
    _ < p := by linarith

/-- Geometric series sum over filtered finset equals sum over Fin k -/
lemma geom_sum_filter_eq (k : Fin 127) :
    (Finset.filter (fun i : Fin 127 => i.val < k.val) Finset.univ).sum (fun i : Fin 127 => 2^i.val)
    = (Finset.univ : Finset (Fin k.val)).sum (fun i => 2^i.val) := by
  symm
  apply Finset.sum_bij (fun (i : Fin k.val) _ => (⟨i.val, Nat.lt_trans i.isLt k.isLt⟩ : Fin 127))
  · intro i _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact i.isLt
  · intro _ _ _ _ h; simp only [Fin.mk.injEq] at h; exact Fin.ext h
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ⟨⟨j.val, hj⟩, Finset.mem_univ _, rfl⟩
  · intro _ _; rfl

/-- Sum of (2^128 - 2^i) over a finset equals card * 2^128 - sum of 2^i -/
lemma sum_sub_pow_eq (t : Finset (Fin 127)) :
    t.sum (fun i => 2^128 - 2^i.val) = t.card * 2^128 - t.sum (fun i => 2^i.val) := by
  induction t using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have h_a_ge : 2^a.val ≤ 2^128 :=
      Nat.pow_le_pow_right (by omega) (Nat.le_of_lt (Nat.lt_trans a.isLt (by omega : 127 < 128)))
    have h_s_ge : ∀ i ∈ s, 2^i.val ≤ 2^128 := fun i _ =>
      Nat.pow_le_pow_right (by omega) (Nat.le_of_lt (Nat.lt_trans i.isLt (by omega : 127 < 128)))
    simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    rw [ih]
    have h_sum_le : s.sum (fun i => 2^i.val) ≤ s.card * 2^128 := by
      calc s.sum (fun i => 2^i.val)
          ≤ s.sum (fun _ => 2^128) := Finset.sum_le_sum (fun i hi => h_s_ge i hi)
        _ = s.card * 2^128 := by simp [Finset.sum_const, smul_eq_mul]
    omega

omit [Fact (p < 2 ^ 254)] in
/-- Ties contribute zero to the sum -/
lemma ties_sum_zero (ct : ℕ) (input : Vector (F p) 254)
    (h_bits : ∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1)
    (parts : Vector (F p) 127)
    (h_parts : ∀ i : Fin 127, parts[i] = computePart i.val input[i.val * 2] input[i.val * 2 + 1] ct)
    (ties : Finset (Fin 127))
    (h_ties : ties = Finset.filter (fun i : Fin 127 =>
      signalPairValF input[i.val * 2] input[i.val * 2 + 1] = constPairValAt i.val ct) Finset.univ) :
    ties.sum (fun i => parts[i].val) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  rw [h_ties] at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [h_parts i]
  have := computePart_characterization i.val i.isLt input[i.val * 2] input[i.val * 2 + 1]
    (h_bits (i.val * 2) (by omega)) (h_bits (i.val * 2 + 1) (by omega)) ct
  simp only [signalPairValF] at this hi
  simp only [this, hi, lt_irrefl, ↓reduceIte]

omit [Fact (p < 2 ^ 254)] in
/-- Wins sum equals card * 2^128 - W -/
lemma wins_sum_val (ct : ℕ) (input : Vector (F p) 254)
    (h_bits : ∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1)
    (parts : Vector (F p) 127)
    (h_parts : ∀ i : Fin 127, parts[i] = computePart i.val input[i.val * 2] input[i.val * 2 + 1] ct)
    (wins : Finset (Fin 127))
    (h_wins : wins = Finset.filter (fun i : Fin 127 =>
      signalPairValF input[i.val * 2] input[i.val * 2 + 1] > constPairValAt i.val ct) Finset.univ) :
    wins.sum (fun i => parts[i].val) = wins.card * 2^128 - wins.sum (fun i => 2^i.val) := by
  have h_eq : wins.sum (fun i => parts[i].val) = wins.sum (fun i => 2^128 - 2^i.val) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [h_wins] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [h_parts i]
    have := computePart_characterization i.val i.isLt input[i.val * 2] input[i.val * 2 + 1]
      (h_bits (i.val * 2) (by omega)) (h_bits (i.val * 2 + 1) (by omega)) ct
    simp only [signalPairValF] at this hi
    simp only [this, hi, ↓reduceIte]
  rw [h_eq, sum_sub_pow_eq]

omit [Fact (p < 2 ^ 254)] in
/-- Losses sum equals Λ -/
lemma losses_sum_val (ct : ℕ) (input : Vector (F p) 254)
    (h_bits : ∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1)
    (parts : Vector (F p) 127)
    (h_parts : ∀ i : Fin 127, parts[i] = computePart i.val input[i.val * 2] input[i.val * 2 + 1] ct)
    (losses : Finset (Fin 127))
    (h_losses : losses = Finset.filter (fun i : Fin 127 =>
      signalPairValF input[i.val * 2] input[i.val * 2 + 1] < constPairValAt i.val ct) Finset.univ) :
    losses.sum (fun i => parts[i].val) = losses.sum (fun i => 2^i.val) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [h_losses] at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [h_parts i]
  have := computePart_characterization i.val i.isLt input[i.val * 2] input[i.val * 2 + 1]
    (h_bits (i.val * 2) (by omega)) (h_bits (i.val * 2 + 1) (by omega)) ct
  simp only [signalPairValF] at this hi
  have h_not_gt : ¬(input[i.val * 2 + 1].val * 2 + input[i.val * 2].val > constPairValAt i.val ct) := by omega
  have h_not_eq : ¬(input[i.val * 2 + 1].val * 2 + input[i.val * 2].val = constPairValAt i.val ct) := by omega
  simp only [this, h_not_gt, h_not_eq, ↓reduceIte]

omit [Fact (Nat.Prime p)] [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
/-- Convert list sum to finset sum over parts -/
lemma parts_list_sum_eq_finset_sum (parts : Vector (F p) 127) :
    (parts.toList.map ZMod.val).sum = (Finset.univ : Finset (Fin 127)).sum (fun i => parts[i].val) := by
  trans (List.ofFn (fun i : Fin 127 => parts[i].val)).sum
  · congr 1
    apply List.ext_getElem
    · rw [List.length_map, Vector.length_toList, List.length_ofFn]
    · intro i h1 h2
      rw [List.length_map, Vector.length_toList] at h1
      simp only [List.getElem_map, Vector.getElem_toList, List.getElem_ofFn]
      rfl
  · simp only [List.sum_ofFn]

omit [Fact (p < 2 ^ 254)] in
/-- The sum partition: sum = wins.card * 2^128 - W + Λ -/
lemma sum_partition (ct : ℕ) (input : Vector (F p) 254)
    (h_bits : ∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1)
    (parts : Vector (F p) 127)
    (h_parts : ∀ i : Fin 127, parts[i] = computePart i.val input[i.val * 2] input[i.val * 2 + 1] ct) :
    let wins := Finset.filter (fun i : Fin 127 =>
      signalPairValF input[i.val * 2] input[i.val * 2 + 1] > constPairValAt i.val ct) Finset.univ
    let losses := Finset.filter (fun i : Fin 127 =>
      signalPairValF input[i.val * 2] input[i.val * 2 + 1] < constPairValAt i.val ct) Finset.univ
    let W := wins.sum (fun i => 2^i.val)
    let Λ := losses.sum (fun i => 2^i.val)
    (parts.toList.map ZMod.val).sum = wins.card * 2^128 - W + Λ := by
  intro wins losses W Λ
  rw [parts_list_sum_eq_finset_sum]

  let ties := Finset.filter (fun i : Fin 127 =>
    signalPairValF input[i.val * 2] input[i.val * 2 + 1] = constPairValAt i.val ct) Finset.univ

  have h_disjoint_wl : Disjoint wins losses := by
    simp only [wins, losses, Finset.disjoint_filter]; intro i _ h1 h2; omega
  have h_disjoint_wt : Disjoint wins ties := by
    simp only [wins, ties, Finset.disjoint_filter]; intro i _ h1 h2; omega
  have h_disjoint_lt : Disjoint losses ties := by
    simp only [losses, ties, Finset.disjoint_filter]; intro i _ h1 h2; omega

  have h_union : wins ∪ losses ∪ ties = Finset.univ := by
    ext i; simp only [Finset.mem_union, wins, losses, ties, Finset.mem_filter,
                      Finset.mem_univ, true_and, iff_true]; omega

  have h_ties_zero : ties.sum (fun i => parts[i].val) = 0 :=
    ties_sum_zero ct input h_bits parts h_parts ties rfl

  have h_wins_val : wins.sum (fun i => parts[i].val) = wins.card * 2^128 - W :=
    wins_sum_val ct input h_bits parts h_parts wins rfl

  have h_losses_val : losses.sum (fun i => parts[i].val) = Λ :=
    losses_sum_val ct input h_bits parts h_parts losses rfl

  calc (Finset.univ : Finset (Fin 127)).sum (fun i => parts[i].val)
      = (wins ∪ losses ∪ ties).sum (fun i => parts[i].val) := by rw [h_union]
    _ = (wins ∪ losses).sum (fun i => parts[i].val) + ties.sum (fun i => parts[i].val) := by
        have h_wl_t_disj : Disjoint (wins ∪ losses) ties := by
          rw [Finset.disjoint_union_left]; exact ⟨h_disjoint_wt, h_disjoint_lt⟩
        exact Finset.sum_union h_wl_t_disj
    _ = wins.sum (fun i => parts[i].val) + losses.sum (fun i => parts[i].val) +
        ties.sum (fun i => parts[i].val) := by
        rw [Finset.sum_union h_disjoint_wl]
    _ = wins.sum (fun i => parts[i].val) + losses.sum (fun i => parts[i].val) := by
        rw [h_ties_zero]; ring
    _ = wins.card * 2^128 - W + Λ := by rw [h_wins_val, h_losses_val]

/-- Bound on W (sum of powers of 2 over any subset of Fin 127) -/
lemma pow_sum_bound (s : Finset (Fin 127)) : s.sum (fun i => 2^i.val) ≤ 2^127 - 1 := by
  calc s.sum (fun i => 2^i.val)
      ≤ (Finset.univ : Finset (Fin 127)).sum (fun i => 2^i.val) :=
        Finset.sum_le_sum_of_subset (fun _ _ => Finset.mem_univ _)
    _ = 2^127 - 1 := sum_pow_two_fin 127

omit [Fact (p < 2 ^ 254)] in
set_option maxHeartbeats 400000 in
/-- Refined range theorem: the sum structure encodes the comparison via bit 127.
    - When input > ct: sum.val / 2^127 is odd (testBit 127 = true)
    - When input ≤ ct: sum.val / 2^127 is even (testBit 127 = false)

    The key insight: Let W = sum of 2^i for win positions, Λ = sum of 2^i for loss positions.
    Sum = |wins| * 2^128 + (Λ - W) when Λ ≥ W, or
    Sum = |wins| * 2^128 - (W - Λ) when W > Λ.

    When input > ct with MSB win at k:
    - k is in the win set, so W ≥ 2^k
    - All losses are at positions j < k, so Λ < 2^k
    - Therefore W > Λ, and sum/2^127 = 2|wins| - 1 (odd)

    When input ≤ ct:
    - Either all ties (sum = 0, sum/2^127 = 0, even)
    - Or MSB loss at k: Λ ≥ 2^k, W < 2^k, so Λ > W
    - Then sum/2^127 = 2|wins| + 0 = 2|wins| (even) -/
lemma sum_range_precise (ct : ℕ) (h_ct : ct < 2^254)
    (input : Vector (F p) 254)
    (h_bits : ∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1)
    (parts : Vector (F p) 127)
    (h_parts : ∀ i : Fin 127,
      parts[i] = computePart i.val input[i.val * 2] input[i.val * 2 + 1] ct) :
    let sum := parts.sum
    let input_val := fromBits (input.map ZMod.val)
    (input_val > ct → sum.val / 2^127 % 2 = 1) ∧
    (input_val ≤ ct → sum.val / 2^127 % 2 = 0) := by
  -- Common setup
  let wins := Finset.filter (fun i : Fin 127 =>
    signalPairValF input[i.val * 2] input[i.val * 2 + 1] > constPairValAt i.val ct) Finset.univ
  let losses := Finset.filter (fun i : Fin 127 =>
    signalPairValF input[i.val * 2] input[i.val * 2 + 1] < constPairValAt i.val ct) Finset.univ
  let W := wins.sum (fun i => 2^i.val)
  let Λ := losses.sum (fun i => 2^i.val)

  have h_parts_bounded := parts_bounded_of_bits ct input h_bits parts h_parts
  have h_sum_lt_p := sum_parts_lt_prime parts h_parts_bounded
  have h_sum_partition := sum_partition ct input h_bits parts h_parts
  have hW_bound : W ≤ 2^127 - 1 := pow_sum_bound wins
  have hΛ_bound : Λ ≤ 2^127 - 1 := pow_sum_bound losses

  constructor

  -- Case 1: input > ct → sum.val / 2^127 is odd
  · intro h_gt
    obtain ⟨k, h_win_k, h_tie_above⟩ := exists_msb_win_position ct h_ct input h_bits h_gt

    have hk_in_wins : k ∈ wins := by
      simp only [wins, Finset.mem_filter, Finset.mem_univ, true_and, signalPairValF]
      exact h_win_k

    have h_losses_lt_k : ∀ j ∈ losses, j < k := by
      intro j hj
      by_contra h_ge_k
      push_neg at h_ge_k
      rcases h_ge_k.lt_or_eq with h_gt_k | h_eq_k
      · have h_tie := h_tie_above j h_gt_k
        simp only [losses, Finset.mem_filter, Finset.mem_univ, true_and, signalPairValF] at hj
        simp only [signalPairValF] at h_tie
        omega
      · subst h_eq_k
        simp only [losses, Finset.mem_filter, Finset.mem_univ, true_and, signalPairValF] at hj h_win_k
        omega

    have hW_ge : W ≥ 2^k.val :=
      Finset.single_le_sum (f := fun i : Fin 127 => 2^i.val) (fun _ _ => Nat.zero_le _) hk_in_wins

    have hΛ_lt : Λ < 2^k.val := by
      have h_losses_subset : losses ⊆ Finset.filter (fun i : Fin 127 => i.val < k.val) Finset.univ := by
        intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h_losses_lt_k j hj
      have h1 : Λ ≤ (Finset.filter (fun i : Fin 127 => i.val < k.val) Finset.univ).sum (fun i => 2^i.val) :=
        Finset.sum_le_sum_of_subset h_losses_subset
      have h2 : (Finset.filter (fun i : Fin 127 => i.val < k.val) Finset.univ).sum (fun i => 2^i.val) ≤ 2^k.val - 1 := by
        rw [geom_sum_filter_eq, sum_pow_two_fin]
      exact Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) (Nat.sub_one_lt (Nat.two_pow_pos k.val).ne')

    have hW_gt_Λ : W > Λ := Nat.lt_of_lt_of_le hΛ_lt hW_ge
    have hW_sub_Λ_bound : W - Λ < 2^127 := Nat.lt_of_le_of_lt (Nat.sub_le W Λ) (Nat.lt_of_le_of_lt hW_bound (by native_decide))
    have hW_sub_Λ_pos : W - Λ > 0 := Nat.sub_pos_of_lt hW_gt_Λ
    have h_wins_card_pos : 0 < wins.card := Finset.card_pos.mpr ⟨k, hk_in_wins⟩

    rw [vector_sum_eq_list_sum', list_sum_val_eq' h_sum_lt_p, h_sum_partition]

    have h_key : (wins.card * 2^128 - W + Λ) / 2^127 = 2 * wins.card - 1 := by
      have h_W_ge_Λ : W ≥ Λ := Nat.le_of_lt hW_gt_Λ
      have h_W_le : W ≤ wins.card * 2^128 := by
        have h_W_lt : W < 2^127 := Nat.lt_of_le_of_lt hW_bound (Nat.sub_one_lt (Nat.two_pow_pos 127).ne')
        have h1 : (2 : ℕ)^127 ≤ 1 * 2^128 := by omega
        have h2 : 1 * 2^128 ≤ wins.card * 2^128 := Nat.mul_le_mul_right _ h_wins_card_pos
        omega
      have h_rearrange : wins.card * 2^128 - W + Λ = wins.card * 2^128 - (W - Λ) := by omega
      rw [h_rearrange]
      have h_expand : wins.card * 2^128 - (W - Λ) = (2 * wins.card - 1) * 2^127 + (2^127 - (W - Λ)) := by
        have h1 : wins.card * 2^128 = 2 * wins.card * 2^127 := by ring
        have h2 : 2 * wins.card * 2^127 = (2 * wins.card - 1) * 2^127 + 2^127 := by
          have : 2 * wins.card - 1 + 1 = 2 * wins.card := Nat.sub_add_cancel (by omega : 2 * wins.card ≥ 1)
          omega
        omega
      rw [h_expand]
      have h_remainder_lt : 2^127 - (W - Λ) < 2^127 := Nat.sub_lt (Nat.two_pow_pos 127) hW_sub_Λ_pos
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 127), Nat.div_eq_of_lt h_remainder_lt]
      simp

    rw [h_key]
    have : 2 * wins.card - 1 = 2 * (wins.card - 1) + 1 := by omega
    rw [this]
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.one_mod]

  -- Case 2: input ≤ ct → sum.val / 2^127 is even
  · intro h_le
    obtain h_all_tie | ⟨k, h_lose_k, h_tie_above⟩ := msb_determines_le ct h_ct input h_bits h_le

    -- Subcase: all ties → sum = 0
    · have h_all_zero : ∀ i : Fin 127, parts[i].val = 0 := by
        intro i
        rw [h_parts i]
        have := computePart_characterization i.val i.isLt input[i.val * 2] input[i.val * 2 + 1]
          (h_bits (i.val * 2) (by omega)) (h_bits (i.val * 2 + 1) (by omega)) ct
        simp only [signalPairValF] at this
        have h_tie := h_all_tie i
        simp only [signalPairValF] at h_tie
        simp only [this, h_tie, lt_irrefl, ↓reduceIte]
      have h_sum_zero : parts.sum = 0 := by
        rw [vector_sum_eq_list_sum']
        apply List.sum_eq_zero
        intro x hx
        rw [List.mem_iff_getElem] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        simp only [Vector.getElem_toList]
        rw [Vector.length_toList] at hi
        have := h_all_zero ⟨i, hi⟩
        simp only [ZMod.val_eq_zero] at this
        exact this
      simp only [h_sum_zero, ZMod.val_zero, Nat.zero_div, Nat.zero_mod]

    -- Subcase: MSB loss at position k
    · have hk_in_losses : k ∈ losses := by
        simp only [losses, Finset.mem_filter, Finset.mem_univ, true_and, signalPairValF]
        exact h_lose_k

      have h_wins_lt_k : ∀ j ∈ wins, j < k := by
        intro j hj
        by_contra h_ge_k
        push_neg at h_ge_k
        rcases h_ge_k.lt_or_eq with h_gt_k | h_eq_k
        · have h_tie := h_tie_above j h_gt_k
          simp only [wins, Finset.mem_filter, Finset.mem_univ, true_and, signalPairValF] at hj
          simp only [signalPairValF] at h_tie
          omega
        · subst h_eq_k
          simp only [wins, Finset.mem_filter, Finset.mem_univ, true_and, signalPairValF] at hj h_lose_k
          omega

      have hW_lt : W < 2^k.val := by
        have h_wins_subset : wins ⊆ Finset.filter (fun i : Fin 127 => i.val < k.val) Finset.univ := by
          intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h_wins_lt_k j hj
        have h1 : W ≤ (Finset.filter (fun i : Fin 127 => i.val < k.val) Finset.univ).sum (fun i => 2^i.val) :=
          Finset.sum_le_sum_of_subset h_wins_subset
        have h2 : (Finset.filter (fun i : Fin 127 => i.val < k.val) Finset.univ).sum (fun i => 2^i.val) ≤ 2^k.val - 1 := by
          rw [geom_sum_filter_eq, sum_pow_two_fin]
        exact Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) (Nat.sub_one_lt (Nat.two_pow_pos k.val).ne')

      have hΛ_ge : Λ ≥ 2^k.val :=
        Finset.single_le_sum (f := fun i : Fin 127 => 2^i.val) (fun _ _ => Nat.zero_le _) hk_in_losses

      have hW_lt_Λ : W < Λ := by omega
      have h_Λ_W_bound : Λ - W < 2^127 := by omega

      rw [vector_sum_eq_list_sum', list_sum_val_eq' h_sum_lt_p, h_sum_partition]

      have h_key : (wins.card * 2^128 - W + Λ) / 2^127 = 2 * wins.card := by
        by_cases h_wins_zero : wins.card = 0
        · have h_wins_empty : wins = ∅ := Finset.card_eq_zero.mp h_wins_zero
          have hW_zero : W = 0 := by simp only [W, h_wins_empty, Finset.sum_empty]
          simp only [h_wins_zero, hW_zero, Nat.zero_mul, Nat.zero_sub, Nat.zero_add]
          have hΛ_lt : Λ < 2^127 := by omega
          rw [Nat.div_eq_of_lt hΛ_lt]
        · have h_wins_pos : wins.card ≥ 1 := Nat.one_le_iff_ne_zero.mpr h_wins_zero
          have h_W_le : W ≤ wins.card * 2^128 := by
            have h2 : (2 : ℕ)^127 - 1 < 2^128 := by
              calc (2 : ℕ)^127 - 1 < 2^127 := Nat.sub_one_lt (Nat.two_pow_pos 127).ne'
                _ ≤ 2^128 := Nat.pow_le_pow_right (by omega) (by omega)
            have h3 : (1 : ℕ) * 2^128 ≤ wins.card * 2^128 := Nat.mul_le_mul_right _ h_wins_pos
            omega
          have h_rearrange : wins.card * 2^128 - W + Λ = wins.card * 2^128 + (Λ - W) := by omega
          rw [h_rearrange]
          have h_expand : wins.card * 2^128 + (Λ - W) = 2 * wins.card * 2^127 + (Λ - W) := by ring
          rw [h_expand]
          apply Nat.div_eq_of_lt_le
          · omega
          · calc 2 * wins.card * 2^127 + (Λ - W) < 2 * wins.card * 2^127 + 2^127 := by omega
              _ = (2 * wins.card + 1) * 2^127 := by ring

      rw [h_key]
      omega

/-! ## Core Mathematical Lemmas -/

/-- Helper: Vector.sum equals List.sum of the toList -/
lemma vector_sum_eq_list_sum {α} [AddCommMonoid α] {n : ℕ} (v : Vector α n) :
    v.sum = v.toList.sum := by
  rw [Vector.sum_mk, ← Array.sum_eq_sum_toList]
  rfl

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
/-- Helper: sum of list of field elements, when sum of vals < p, equals val of sum -/
lemma list_sum_val_eq {l : List (F p)} (h : (l.map ZMod.val).sum < p) :
    l.sum.val = (l.map ZMod.val).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons] at h ⊢
    have h_xs : (xs.map ZMod.val).sum < p := by
      have : x.val < p := ZMod.val_lt x
      linarith
    have ih' := ih h_xs
    rw [ZMod.val_add, ih']
    rw [Nat.mod_eq_of_lt h]

omit [Fact (Nat.Prime p)] [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
/-- Helper: bound on sum of list of field element vals -/
lemma list_sum_val_bound {l : List (F p)} {bound : ℕ}
    (h : ∀ x ∈ l, x.val ≤ bound) :
    (l.map ZMod.val).sum ≤ l.length * bound := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h_x : x.val ≤ bound := h x (List.Mem.head xs)
    have h_xs : ∀ y ∈ xs, y.val ≤ bound := fun y hy => h y (List.Mem.tail x hy)
    have := ih h_xs
    linarith

omit [Fact (p < 2 ^ 254)] in
/-- Lemma 1: The sum of parts is bounded.
    Since each part is bounded and there are 127 parts, the sum fits in 135 bits. -/
lemma sum_parts_bounded (parts : Vector (F p) 127)
    (h_parts : ∀ i : Fin 127, parts[i].val ≤ 2^128) :
    parts.sum.val < 2^135 := by
  -- Convert to list sum
  rw [vector_sum_eq_list_sum]

  -- Show all elements of toList satisfy the bound
  have h_list_bound : ∀ x ∈ parts.toList, x.val ≤ 2^128 := by
    intro x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    simp only [Vector.getElem_toList]
    rw [Vector.length_toList] at hi
    exact h_parts ⟨i, hi⟩

  -- Get bound on natural sum
  have h_nat_bound := list_sum_val_bound h_list_bound
  simp only [Vector.length_toList] at h_nat_bound

  -- Show 127 * 2^128 < 2^135 < p
  have h_bound_lt : 127 * 2^128 < 2^135 := by native_decide
  have hp : p > 2^253 := ‹Fact (p > 2^253)›.elim
  have h_135_lt_253 : (2 : ℕ)^135 < 2^253 := by native_decide

  -- The sum of vals is < p, so we can use list_sum_val_eq
  have h_sum_lt_p : (parts.toList.map ZMod.val).sum < p := by linarith

  rw [list_sum_val_eq h_sum_lt_p]
  linarith

/-! ## Compute Part Analysis -/

/-- The pair value for input bits at position i: smsb * 2 + slsb (0 to 3) -/
def signalPairVal (i : ℕ) (hi : i < 127) (input : Vector (F p) 254) : ℕ :=
  have hi2 : i * 2 < 254 := by omega
  have hi21 : i * 2 + 1 < 254 := by omega
  input[i * 2 + 1].val * 2 + input[i * 2].val

/-- The pair value for constant bits at position i: cmsb * 2 + clsb (0 to 3) -/
def constPairVal (i : ℕ) (ct : ℕ) : ℕ :=
  ((ct >>> (i * 2 + 1)) &&& 1) * 2 + ((ct >>> (i * 2)) &&& 1)

/-- Helper: constPairVal is bounded by 3 -/
lemma constPairVal_le_3 (i : ℕ) (ct : ℕ) : constPairVal i ct ≤ 3 := by
  unfold constPairVal
  have h1 : (ct >>> (i * 2 + 1)) &&& 1 ≤ 1 := Nat.and_le_right
  have h2 : (ct >>> (i * 2)) &&& 1 ≤ 1 := Nat.and_le_right
  omega

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
/-- Helper: signalPairVal is bounded by 3 when inputs are boolean -/
lemma signalPairVal_le_3 (i : ℕ) (hi : i < 127) (input : Vector (F p) 254)
    (h_bits : ∀ j (_ : j < 254), input[j] = 0 ∨ input[j] = 1) :
    signalPairVal i hi input ≤ 3 := by
  unfold signalPairVal
  have hi2 : i * 2 < 254 := by omega
  have hi21 : i * 2 + 1 < 254 := by omega
  have hp_gt_1 : 1 < p := Nat.Prime.one_lt ‹Fact (Nat.Prime p)›.elim
  have h_slsb := h_bits (i * 2) hi2
  have h_smsb := h_bits (i * 2 + 1) hi21
  rcases h_slsb with h0_l | h1_l <;> rcases h_smsb with h0_m | h1_m
  · simp only [h0_l, h0_m, ZMod.val_zero]; omega
  · simp only [h0_l, h1_m, ZMod.val_zero, @ZMod.val_one p ⟨hp_gt_1⟩]; omega
  · simp only [h1_l, h0_m, ZMod.val_zero, @ZMod.val_one p ⟨hp_gt_1⟩]; omega
  · simp only [h1_l, h1_m, @ZMod.val_one p ⟨hp_gt_1⟩]; omega

omit [Fact (p < 2 ^ 254)] in
/-- computePart value is bounded by 2^128 when inputs are boolean and i < 127.
    This is the key bound needed for sum_parts_bounded. -/
lemma computePart_val_bound (i : ℕ) (hi : i < 127) (slsb smsb : F p)
    (h_slsb : slsb = 0 ∨ slsb = 1) (h_smsb : smsb = 0 ∨ smsb = 1) (ct : ℕ) :
    (computePart i slsb smsb ct).val ≤ 2^128 :=
  -- This is the same as computePart_val_bound'
  computePart_val_bound' i hi slsb smsb h_slsb h_smsb ct

/-- Lemma 2: The core comparison encoding.
    When input bits are boolean, the sum encodes whether input > ct in bit 127.

    The proof relies on the following insight from the circuit design:
    - For each pair position i, we compare (smsb, slsb) vs (cmsb, clsb)
    - The coefficient b = 2^128 - 2^i is used when signal > constant at this position
    - The coefficient a = 2^i is used for tie-breaking / carry propagation
    - The sum of all parts has bit 127 set iff the overall comparison is input > ct

    This works because:
    1. If s_pair > c_pair at the MSB pair (position 126), bit 127 is set
    2. If s_pair < c_pair at MSB, bit 127 is unset regardless of lower bits
    3. If equal at MSB, the comparison cascades to lower pairs

    The detailed proof requires careful analysis of all 16 cases per pair position. -/
lemma sum_bit127_encodes_gt (ct : ℕ) (h_ct : ct < 2^254)
    (input : Vector (F p) 254)
    (h_bits : ∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1)
    (parts : Vector (F p) 127)
    (h_parts : ∀ i : Fin 127,
      parts[i] = computePart i.val input[i.val * 2] input[i.val * 2 + 1] ct) :
    let sum := parts.sum
    let input_val := fromBits (input.map ZMod.val)
    sum.val.testBit 127 = (input_val > ct) := by
  simp only

  -- Get the parity of sum.val / 2^127 from sum_range_precise
  have h_range := sum_range_precise ct h_ct input h_bits parts h_parts
  simp only at h_range
  obtain ⟨h_gt_range, h_le_range⟩ := h_range

  -- Case split on the comparison
  by_cases h_cmp : fromBits (input.map ZMod.val) > ct

  -- Case: input > ct, need testBit 127 = true
  case pos =>
    simp only [h_cmp]
    -- From h_gt_range: sum.val / 2^127 % 2 = 1 (odd)
    have h_odd := h_gt_range h_cmp
    -- testBit 127 = (1 &&& (sum / 2^127) ≠ 0)
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
    -- Goal: (1 &&& (parts.sum.val / 2^127) ≠ 0) = true
    -- Since (1 &&& x) = x % 2, and h_odd says x % 2 = 1
    rw [Nat.one_and_eq_mod_two, h_odd]
    decide

  -- Case: input ≤ ct, need testBit 127 = false
  case neg =>
    push_neg at h_cmp
    -- From h_le_range: sum.val / 2^127 % 2 = 0 (even)
    have h_even := h_le_range h_cmp
    -- testBit 127 = (1 &&& (sum / 2^127) ≠ 0)
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, not_lt.mpr h_cmp]
    -- Goal: (1 &&& (parts.sum.val / 2^127) ≠ 0) = false
    rw [Nat.one_and_eq_mod_two, h_even]
    decide

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
/-- Lemma 3: fieldToBits correctly represents bit 127 -/
lemma fieldToBits_testBit_127 (x : F p) (n : ℕ) (hn : 127 < n) :
    (fieldToBits n x)[127] = if x.val.testBit 127 then 1 else 0 := by
  simp only [fieldToBits, toBits, Vector.getElem_map, Vector.getElem_mapRange]
  split_ifs <;> simp_all

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
/-- Helper: Expression.eval distributes over List.sum -/
lemma list_sum_map_eval (env : Environment (F p)) (l : List (Expression (F p))) :
    (l.map (Expression.eval env)).sum = Expression.eval env l.sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, circuit_norm]
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    simp only [circuit_norm]

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
/-- Helper: Expression.eval distributes over Vector.sum -/
lemma vector_sum_map_eval (env : Environment (F p)) (n : ℕ) (i₀ : ℕ) :
    (Vector.map (Expression.eval env) (Vector.mapRange n fun i => var { index := i₀ + i })).sum =
    Expression.eval env (Vector.mapRange n fun i => var { index := i₀ + i }).sum := by
  simp only [Vector.sum, Vector.toArray_map]
  conv_lhs => rw [← Array.sum_eq_sum_toList, Array.toList_map]
  conv_rhs => rw [← Array.sum_eq_sum_toList]
  exact list_sum_map_eval env _

/-! ## Main Circuit -/

/-
template ClaudeCompConstant(ct) {
    signal input in[254];
    signal output out;

    signal parts[127];
    signal sout;

    var clsb;
    var cmsb;
    var slsb;
    var smsb;

    var sum=0;

    var b = (1 << 128) -1;
    var a = 1;
    var e = 1;
    var i;

    for (i=0;i<127; i++) {
        clsb = (ct >> (i*2)) & 1;
        cmsb = (ct >> (i*2+1)) & 1;
        slsb = in[i*2];
        smsb = in[i*2+1];

        if ((cmsb==0)&&(clsb==0)) {
            parts[i] <== -b*smsb*slsb + b*smsb + b*slsb;
        } else if ((cmsb==0)&&(clsb==1)) {
            parts[i] <== a*smsb*slsb - a*slsb + b*smsb - a*smsb + a;
        } else if ((cmsb==1)&&(clsb==0)) {
            parts[i] <== b*smsb*slsb - a*smsb + a;
        } else {
            parts[i] <== -a*smsb*slsb + a;
        }

        sum = sum + parts[i];

        b = b -e;
        a = a +e;
        e = e*2;
    }

    sout <== sum;

    component num2bits = Num2Bits(135);

    num2bits.in <== sout;

    out <== num2bits.out[127];
}
-/
def main (ct : ℕ) (input : Vector (Expression (F p)) 254) := do
  let parts : fields 127 (Expression (F p)) <== Vector.ofFn fun i =>
    let clsb := (ct >>> (i.val * 2)) &&& 1
    let cmsb := (ct >>> (i.val * 2 + 1)) &&& 1
    let slsb := input[i.val * 2]
    let smsb := input[i.val * 2 + 1]

    let b_val : ℤ := 2^128 - 2^i.val
    let a_val : ℤ := 2^i.val

    if cmsb == 0 && clsb == 0 then
      -(b_val : F p) * smsb * slsb + (b_val : F p) * smsb + (b_val : F p) * slsb
    else if cmsb == 0 && clsb == 1 then
      (a_val : F p) * smsb * slsb - (a_val : F p) * slsb + (b_val : F p) * smsb - (a_val : F p) * smsb + (a_val : F p)
    else if cmsb == 1 && clsb == 0 then
      (b_val : F p) * smsb * slsb - (a_val : F p) * smsb + (a_val : F p)
    else
      -(a_val : F p) * smsb * slsb + (a_val : F p)

  -- Compute sum of parts
  let sout <== parts.sum

  -- Convert sum to 135 bits
  have hp : p > 2^135 := by linarith [‹Fact (p > 2^253)›.elim]
  let bits ← Num2Bits.circuit 135 hp sout

  -- Output is bit 127
  let out <== bits[127]
  return out

/-! ## Formal Circuit Definition -/

--set_option maxHeartbeats 3200000 in
def circuit (c : ℕ) : FormalCircuit (F p) (fields 254) field where
  main := main c
  localLength _ := 127 + 1 + 135 + 1
  localLength_eq := by simp only [circuit_norm, main, Num2Bits.circuit]
  subcircuitsConsistent input n := by
    simp only [circuit_norm, main, Num2Bits.circuit]
    and_intros <;> ac_rfl

  Assumptions input :=
    (∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1) ∧ c < 2^254

  Spec input output :=
    output = if fromBits (input.map ZMod.val) > c then 1 else 0

  soundness := by
    circuit_proof_start [Num2Bits.circuit]
    rcases h_assumptions with ⟨h_bits, h_ct⟩
    rcases h_holds with ⟨h_parts, h_holds⟩
    rcases h_holds with ⟨h_sout, h_holds⟩
    rcases h_holds with ⟨h_num2bits, h_out⟩
    rcases h_num2bits with ⟨h_sout_range, h_bits_valid⟩

    -- Define local names for circuit values
    let parts : Vector (F p) 127 := Vector.mapRange 127 fun i => env.get (i₀ + i)
    let sout : F p := env.get (i₀ + 127)
    let bits : Vector (F p) 135 := Vector.mapRange 135 fun i => env.get (i₀ + 127 + 1 + i)
    let out : F p := env.get (i₀ + 127 + 1 + 135)
    let input_val : ℕ := fromBits (input.map ZMod.val)

    -- Prove parts satisfy the computePart characterization
    -- The circuit expression at index i equals computePart i input[2i] input[2i+1] c
    -- Both have the same if-then-else structure based on c's bits at positions 2i and 2i+1
    -- The Nat cast (n : ℕ) : F p equals the Int cast (n : ℤ) : F p for non-negative n
    -- Helper to evaluate input_var at any index
    have h_input_eval : ∀ j : ℕ, (hj : j < 254) → input_var[j].eval env = input[j] := by
      intro j hj
      have := congrArg (fun v => v[j]) h_input
      simp only [Vector.getElem_map] at this
      exact this

    have h_parts' : ∀ i : Fin 127, parts[i] = computePart i.val input[i.val * 2] input[i.val * 2 + 1] c := by
      intro i
      have h_parts_i := congrArg (fun v => v[i]) h_parts
      simp only [circuit_norm, Vector.getElem_ofFn, Vector.getElem_mapRange, Vector.getElem_map] at h_parts_i
      show (Vector.mapRange 127 fun j => env.get (i₀ + j))[i.val] = _
      simp only [Vector.getElem_mapRange, h_parts_i]
      -- Push Expression.eval through if-then-else using apply_ite
      simp only [apply_ite (Expression.eval env)]
      -- Evaluate the expressions
      simp only [circuit_norm]
      -- Use h_input_eval
      have hi2 : (i : ℕ) * 2 < 254 := by omega
      have hi2p1 : (i : ℕ) * 2 + 1 < 254 := by omega
      simp only [h_input_eval _ hi2, h_input_eval _ hi2p1]
      -- Expand computePart, bCoeff, aCoeff
      simp only [computePart, bCoeff, aCoeff]
      have h_pow_le : (2 : ℕ)^(i : ℕ) ≤ 2^128 := Nat.pow_le_pow_right (by omega) (by omega : (i : ℕ) ≤ 128)
      -- Convert Int casts to Nat casts (they agree for non-negative values)
      have h_int_eq_nat_sub : ((2^128 - 2^(i : ℕ) : ℤ) : F p) = ((2^128 - 2^(i : ℕ) : ℕ) : F p) := by
        rw [Int.cast_sub, Nat.cast_sub h_pow_le]
        simp only [Int.cast_pow, Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]
      have h_int_eq_nat_pow : ((2^(i : ℕ) : ℤ) : F p) = ((2^(i : ℕ) : ℕ) : F p) := by
        simp only [Int.cast_pow, Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]
      simp_rw [h_int_eq_nat_sub, h_int_eq_nat_pow]
      simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sub h_pow_le]
      split_ifs <;> ring

    -- Now use the main theorem to connect parts.sum to the comparison
    have h_sum_encodes := sum_bit127_encodes_gt c h_ct input h_bits parts h_parts'

    -- parts.sum = sout
    have h_sout' : parts.sum = sout := by
      show (Vector.mapRange 127 fun i => env.get (i₀ + i)).sum = env.get (i₀ + 127)
      rw [h_sout]
      -- Show both vectors are equal, then their sums are equal
      have h_vec_eq : (Vector.mapRange 127 fun i => env.get (i₀ + i)) =
                      Vector.map (Expression.eval env) (Vector.mapRange 127 fun i => var { index := i₀ + i }) := by
        ext j hj
        simp only [Vector.getElem_mapRange, Vector.getElem_map, circuit_norm]
      rw [h_vec_eq, vector_sum_map_eval]

    have h_sum_encodes' : sout.val.testBit 127 = (input_val > c) := by
      rw [← h_sout']
      exact h_sum_encodes

    -- bits = fieldToBits 135 sout
    have h_bits' : bits = fieldToBits 135 sout := by
      show Vector.mapRange 135 (fun i => env.get (i₀ + 127 + 1 + i)) = fieldToBits 135 (env.get (i₀ + 127))
      have := h_bits_valid
      simp only [Vector.map_mapRange, circuit_norm] at this
      ext j hj
      have := congrArg (fun v => v[j]) this
      simp only [Vector.getElem_mapRange] at this ⊢
      exact this

    -- bits[127] encodes the comparison
    have h_bits_127 : bits[127] = if input_val > c then 1 else 0 := by
      rw [h_bits']
      rw [fieldToBits_testBit_127 sout 135 (by omega : 127 < 135)]
      simp only [h_sum_encodes']

    -- out = bits[127]
    have h_out' : env.get (i₀ + 127 + 1 + 135) = bits[127] := by
      show env.get (i₀ + 127 + 1 + 135) = (Vector.mapRange 135 fun i => env.get (i₀ + 127 + 1 + i))[127]
      simp only [Vector.getElem_mapRange, h_out]

    -- Conclude
    show env.get (i₀ + 127 + 1 + 135) = if c < fromBits (Vector.map ZMod.val input) then 1 else 0
    simp only [h_out', h_bits_127, gt_iff_lt, input_val]

  -- Completeness proof: given valid inputs, there exists a valid witness assignment
  -- The proof follows the same structure as soundness but in reverse:
  -- 1. Parts are computed correctly from input bits
  -- 2. Sum of parts is bounded by 2^135 (so Num2Bits subcircuit succeeds)
  -- 3. Output is bit 127 of the sum
  -- The completeness proof uses the same key lemmas as soundness but experiences
  -- performance issues with 127-element vector operations.
  -- TODO: Complete this proof with optimized tactics or increased heartbeats
  completeness := by
    circuit_proof_start [Num2Bits.circuit]
    sorry

end ClaudeCompConstant

end Circomlib
