module

public import ConditionalGoldbach.Proofs.Elementary
import Mathlib.Tactic

/-! Bounds for Li–Liu's singular series using its finite correction product. -/

open ConditionalGoldbach Finset Filter Real
open MathlibNt.SieveTheory.SingularSeries

@[expose] public section

noncomputable section

namespace PrescribedSWidth

private theorem prod_correctionFactor_le (P : Finset ℕ) (hP : ∀ p ∈ P, 2 < p) :
    ∏ p ∈ P, liuCorrectionFactor p ≤ (P.card : ℝ) + 1 := by
  induction P using Finset.induction_on_max with
  | empty => simp
  | insert p P hp ih =>
    have hp₂ := hP p (mem_insert_self _ _)
    have hsub : P ⊆ Ico 3 p := by
      intro q hq
      exact mem_Ico.2 ⟨hP q (mem_insert_of_mem hq), hp q hq⟩
    have hcard := card_le_card hsub
    rw [Nat.card_Ico] at hcard
    have hpbound : (P.card : ℝ) + 3 ≤ p := by
      exact_mod_cast (show P.card + 3 ≤ p by omega)
    have hpout : p ∉ P := fun hp' => (lt_irrefl p) (hp p hp')
    have hp' : (2 : ℝ) < p := by exact_mod_cast hp₂
    have hfactor : liuCorrectionFactor p ≤ ((P.card : ℝ) + 2) / (P.card + 1) := by
      unfold liuCorrectionFactor
      apply (div_le_div_iff₀ (by linarith) (by positivity)).2
      nlinarith
    rw [prod_insert hpout, card_insert_of_notMem hpout, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ (((P.card : ℝ) + 2) / (P.card + 1)) * ((P.card : ℝ) + 1) :=
        mul_le_mul hfactor (ih (fun q hq => hP q (mem_insert_of_mem hq)))
          (prod_nonneg fun q hq => (liuCorrectionFactor_pos (hP q (mem_insert_of_mem hq))).le)
          (by positivity)
      _ = _ := by rw [div_mul_cancel₀ _ (by positivity)]; ring

/-- A logarithmic upper bound suffices for the endpoint of the prescribed widths. -/
theorem singularSeries_le_log {N : ℕ} (hN : 0 < N) (hL : 1 ≤ log (N : ℝ)) :
    ConditionalGoldbach.singularSeries N ≤ (2 * C2 * (1 + (log 2)⁻¹)) * log N := by
  let P := N.primeFactors.filter fun p => 2 < p
  have hP : ∀ p ∈ P, 2 < p := fun _ hp => (mem_filter.1 hp).2
  have hdvd : (∏ p ∈ P, p) ∣ N := by
    exact (Finset.prod_dvd_prod_of_subset P N.primeFactors id (filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd N)
  have hpow : 2 ^ P.card ≤ N := by
    calc
      _ = ∏ _ ∈ P, 2 := (prod_const 2).symm
      _ ≤ ∏ p ∈ P, p := Finset.prod_le_prod fun p hp => (hP p hp).le
      _ ≤ N := Nat.le_of_dvd hN hdvd
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ P.card)
    (show (2 : ℝ) ^ P.card ≤ N by exact_mod_cast hpow)
  rw [Real.log_pow] at hlog
  have hl2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hcard : (P.card : ℝ) ≤ log N / log 2 := (le_div_iff₀ hl2).2 hlog
  have hcorr : liuCorrection N ≤ (P.card : ℝ) + 1 := prod_correctionFactor_le P hP
  have hcoeff : (P.card : ℝ) + 1 ≤ (1 + (log 2)⁻¹) * log N := by
    rw [add_mul, one_mul, inv_mul_eq_div]
    linarith
  have hc : 0 ≤ 2 * C2 := mul_nonneg (by norm_num) C2_pos.le
  rw [singularSeries_eq_existing, liuSingularSeries]
  change 2 * (liuCorrection N * C2) ≤ _
  calc
    _ = (2 * C2) * liuCorrection N := by ring
    _ ≤ (2 * C2) * ((1 + (log 2)⁻¹) * log N) :=
      mul_le_mul_of_nonneg_left (hcorr.trans hcoeff) hc
    _ = _ := by ring

/-- The finite correction is close to 1 whenever the sum of the reciprocals
of the shifted odd prime divisors is small. -/
theorem singularSeries_le_exp_divisor_sum (N : ℕ) :
    ConditionalGoldbach.singularSeries N ≤ 2 * C2 *
      exp (∑ p ∈ N.primeFactors.filter (fun p => 2 < p), ((p : ℝ) - 2)⁻¹) := by
  have hc : 0 ≤ 2 * C2 := mul_nonneg (by norm_num) C2_pos.le
  rw [singularSeries_eq_existing, liuSingularSeries]
  change 2 * (liuCorrection N * C2) ≤ _
  rw [show 2 * (liuCorrection N * C2) = (2 * C2) * liuCorrection N by ring]
  apply mul_le_mul_of_nonneg_left _ hc
  rw [liuCorrection, Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro p hp
    exact (liuCorrectionFactor_pos (mem_filter.1 hp).2).le
  · intro p hp
    have h2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.1 hp).2
    have hne : (p : ℝ) - 2 ≠ 0 := sub_ne_zero.2 h2.ne'
    unfold liuCorrectionFactor
    rw [show ((p : ℝ) - 1) / ((p : ℝ) - 2) = ((p : ℝ) - 2)⁻¹ + 1 by field_simp; ring]
    exact Real.add_one_le_exp _

end PrescribedSWidth

end

end
