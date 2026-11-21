module

public import PrescribedSWidth.Scales
public import ConditionalGoldbach.Proofs.DictionaryApplication

/-! Conversion of the second-order norm lower bound to failure of the actual
Li–Liu zero-free condition. -/

open ConditionalGoldbach Filter Real
open scoped Topology

namespace PrescribedSWidth

@[expose] public section

noncomputable section

def prescribedWidth (a d : ℝ) (N : ℕ) : ℝ :=
  sqrt N * exp (-widthExponent a d (log N))

theorem prescribedWidth_first_eq (d : ℝ) (N : ℕ) (hl : log (log N) ≠ 0) :
    prescribedWidth (d/sqrt 2) 0 N = sqrt N * exp (-(d * sqrt (log N) / log (log N))) := by
  unfold prescribedWidth widthExponent secondScale
  rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
  have hs : sqrt (2 : ℝ) ≠ 0 := by positivity
  congr 3
  field_simp
  simp

theorem prescribedWidth_second_eq (d : ℝ) (N : ℕ) (hl : log (log N) ≠ 0) :
    prescribedWidth 1 d N =
      sqrt N * exp (-(sqrt (2*log N) / log (log N) * (1 + d/log (log N)))) := by
  unfold prescribedWidth widthExponent secondScale
  congr 3
  field_simp

def GlobalGRH : Prop := ∀ N : ℕ, 0 < N → GRH N

/-- The norm bound (10) in exponentiated form. The expressions use Li–Liu's
actual residual operator on the strip with left boundary `1/log N`. -/
def StrongNormBound (C : ℝ) (N : ℕ) : Prop :=
  ∀ (_ : NeZero N) (ha : alpha N < beta),
    exp (normExponent C (log N)) ≤ sqrt N * ‖residualOperator ha N‖

private theorem eventually_even {P : ℕ → Prop} (h : ∀ᶠ N in atTop, P N) :
    EvenEventually P := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 h
  exact ⟨N₀, fun N hN _ => hN₀ N hN⟩

private theorem tendsto_log_nat : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem width_pos (a d : ℝ) {N : ℕ} (hN : 0 < N) :
    0 < prescribedWidth a d N := by
  exact mul_pos (sqrt_pos.2 (by exact_mod_cast hN)) (exp_pos _)

theorem prescribedWidth_isAdmissible {a : ℝ} (ha : 0 < a) (d : ℝ) :
    IsAdmissible (prescribedWidth a d) := by
  refine ⟨fun N _ hN => width_pos a d (by omega), ?_, ?_⟩
  · intro B
    apply eventually_even
    have hquarter := tendsto_log_nat.eventually (eventually_widthExponent_le_quarter ha.le d)
    have hexp : Tendsto (fun N : ℕ => exp (log (N : ℝ) / 4)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_log_nat.atTop_div_const (by norm_num))
    filter_upwards [hquarter, hexp.eventually_ge_atTop B, eventually_gt_atTop (0 : ℕ)]
      with N hN hB hpos
    have hn : 0 < (N : ℝ) := by exact_mod_cast hpos
    have hs : sqrt (N : ℝ) = exp (log N / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn]
      congr 1
      ring
    apply hB.trans
    rw [prescribedWidth, hs, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  · let c := 2 * C2
    have hc : 0 < c := mul_pos (by norm_num) C2_pos
    have hbig := tendsto_log_nat.eventually
      (eventually_widthExponent_large ha d (3 / 2) (log (4 / c) / 2))
    apply eventually_even
    filter_upwards [hbig, tendsto_log_nat.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ)]
      with N hb hL hN
    have hn : 0 < (N : ℝ) := by exact_mod_cast hN
    have hS := singularSeries_pos N
    have hSc : c ≤ singularSeries N := singularSeries_uniform_lower N
    have he : log N ^ 3 * (4 / c) ≤ exp (2 * widthExponent a d (log N)) := by
      have hb' : 3 * log (log N) + log (4 / c) ≤ 2 * widthExponent a d (log N) := by
        linarith
      have h := exp_le_exp.2 hb'
      rw [exp_add, show (3 : ℝ) = (3 : ℕ) by norm_num, exp_nat_mul,
        exp_log hL, exp_log (div_pos (by norm_num) hc)] at h
      exact h
    unfold zeroFreeWidth prescribedWidth
    rw [mul_pow, sq_sqrt hn.le,
      ← exp_nat_mul, show (↑(2 : ℕ) : ℝ) * -widthExponent a d (log N) =
        -(2 * widthExponent a d (log N)) by ring, exp_neg,
      mul_assoc, mul_div_mul_left _ _ hn.ne']
    apply (div_le_iff₀ hS).2
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ (exp_pos _)).2
    have h₁ : log N ^ 3 * 4 ≤ exp (2 * widthExponent a d (log N)) * c :=
      (div_le_iff₀ hc).1 (by rwa [← mul_div_assoc] at he)
    have h₂ := mul_le_mul_of_nonneg_left hSc (exp_pos (2 * widthExponent a d (log N))).le
    nlinarith

/-- Theorem 6.1 after substituting `η = h² (log N)³ / (N · singularSeries N)`. -/
theorem spectralZeroFree_iff_prescribed_bound (N : ℕ) [NeZero N] (he : Even N)
    (hlarge : exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta)
    (h : ℕ → ℝ) (hh : 0 < h N) (hη : zeroFreeWidth N h ≤ 1 / 4) :
    SpectralZeroFree N (alpha N) ha (zeroFreeWidth N h) ↔
      ‖residualOperator ha N‖ ≤
        singularSeries N / (2 * h N * sqrt (1 - zeroFreeWidth N h)) := by
  have hL := (large_parameters hlarge).2.1
  have hn : 0 < (N : ℝ) := (exp_pos 10).trans hlarge
  have hS := singularSeries_pos N
  have hηpos : 0 < zeroFreeWidth N h :=
    div_pos (mul_pos (sq_pos_of_pos hh) (pow_pos hL _)) (mul_pos hn hS)
  have haη : zeroFreeWidth N h < 1 / 2 := by linarith
  have hroot : 0 < sqrt (1 - zeroFreeWidth N h) := sqrt_pos.2 (by linarith)
  have hscale : 0 ≤ spectralScale N :=
    mul_nonneg (sqrt_nonneg _) (Real.rpow_nonneg hL.le _)
  have hscaleSq : spectralScale N ^ 2 = (singularSeries N / N) * log N ^ 3 := by
    unfold spectralScale
    simp only [Real.rpow_eq_pow]
    rw [mul_pow, sq_sqrt (div_nonneg hS.le hn.le), ← Real.rpow_mul_natCast hL.le,
      show (3 / 2 : ℝ) * (↑(2 : ℕ) : ℝ) = (↑(3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hcross : spectralScale N * h N = singularSeries N * sqrt (zeroFreeWidth N h) := by
    apply (sq_eq_sq₀ (mul_nonneg hscale hh.le) (by positivity)).1
    rw [mul_pow, mul_pow, hscaleSq, sq_sqrt hηpos.le, zeroFreeWidth]
    field_simp
  rw [(theorem_6_1 N he hlarge hGRH ha).2.1 _ hηpos haη, sqrt_mul hηpos.le]
  have heq : spectralScale N / (2 * (sqrt (zeroFreeWidth N h) * sqrt (1 - zeroFreeWidth N h))) =
      singularSeries N / (2 * h N * sqrt (1 - zeroFreeWidth N h)) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    linear_combination 2 * sqrt (1 - zeroFreeWidth N h) * hcross
  rw [heq]

/-- An unbounded supply of moduli having (10) forces failure of the prescribed
zero-free condition. The singular-series bound needed here is merely `O(log N)`. -/
theorem not_hypothesisS_of_normBound {a d C D : ℝ} (ha : 0 < a) (ha' : a ≤ 1)
    (hd : d < 2 + log 2) (hD : 0 < D) (hGRH : GlobalGRH)
    (hS : EvenEventually (fun N => singularSeries N ≤ D * log N))
    (hbound : ∀ K : ℕ, ∃ N ≥ K, Even N ∧ StrongNormBound C N) :
    ¬ HypothesisS (prescribedWidth a d) := by
  intro h
  have hgap : EvenEventually (fun N => log (log N) + log D <
      normExponent C (log N) - widthExponent a d (log N)) := by
    apply eventually_even
    simpa only [one_mul] using
      tendsto_log_nat.eventually (eventually_normExponent_gap ha' hd C 1 (log D))
  obtain ⟨K, hK⟩ := (((evenEventually_large.and hgap).and hS).and
    (prescribedWidth_isAdmissible ha d).2.2).and h.2
  obtain ⟨N, hNK, he, hNbound⟩ := hbound K
  obtain ⟨⟨⟨⟨hlarge, hgap'⟩, hs⟩, hwidth⟩, hScond⟩ := hK N hNK he
  rcases large_parameters hlarge with ⟨hN4, hL, hstrip⟩
  have hN : 0 < N := by omega
  have : NeZero N := ⟨hN.ne'⟩
  have hGRHN := hGRH N hN
  have hpos := width_pos a d hN
  have hzero := hScond hGRHN (inferInstance : NeZero N) hstrip
  have hupper := (spectralZeroFree_iff_prescribed_bound N he hlarge hGRHN hstrip
    (prescribedWidth a d) hpos hwidth).1 hzero
  have hden : 1 ≤ 2 * sqrt (1 - zeroFreeWidth N (prescribedWidth a d)) := by
    have hsqrt : 1 / 2 ≤ sqrt (1 - zeroFreeWidth N (prescribedWidth a d)) := by
      rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact sqrt_le_sqrt (by nlinarith)
    linarith
  have hupper' : prescribedWidth a d N * ‖residualOperator hstrip N‖ ≤ singularSeries N := by
    have hprod : prescribedWidth a d N ≤
        2 * prescribedWidth a d N * sqrt (1 - zeroFreeWidth N (prescribedWidth a d)) := by
      nlinarith [mul_le_mul_of_nonneg_left hden hpos.le]
    have hmul := (le_div_iff₀ (hpos.trans_le hprod)).1 hupper
    calc
      _ ≤ ‖residualOperator hstrip N‖ *
          (2 * prescribedWidth a d N * sqrt (1 - zeroFreeWidth N (prescribedWidth a d))) := by
        rw [mul_comm (prescribedWidth a d N)]
        exact mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ ≤ _ := hmul
  have he := exp_lt_exp.2 hgap'
  rw [exp_add, exp_log hL, exp_log hD, sub_eq_add_neg, exp_add] at he
  have hmul := mul_le_mul_of_nonneg_right (hNbound inferInstance hstrip)
    (exp_pos (-widthExponent a d (log N))).le
  have hcontr : singularSeries N < prescribedWidth a d N * ‖residualOperator hstrip N‖ := by
    refine hs.trans_lt ((mul_comm D (log N) ▸ he).trans_le ?_)
    unfold prescribedWidth
    convert hmul using 1
    ring
  exact (not_lt_of_ge hupper') hcontr

end

end

end PrescribedSWidth
