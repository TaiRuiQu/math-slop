module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Parameters in the second-order norm bound and the prescribed widths.
Here `L` is the logarithm of the original variable, not the original variable. -/

open Filter Real
open scoped Topology

namespace PrescribedSWidth

@[expose] public section

noncomputable section

def secondScale (L : ℝ) : ℝ := sqrt (2 * L) / log L ^ 2

theorem secondScale_nonneg (L : ℝ) : 0 ≤ secondScale L := by
  unfold secondScale
  positivity

/-- The exponential loss in a prescribed width. The leading coefficient is
measured in units of `√(2L) / log L`. -/
def widthExponent (a d L : ℝ) : ℝ := (a * log L + d) * secondScale L

def normExponent (C L : ℝ) : ℝ := widthExponent 1 (2 + log 2 - C / log L) L

theorem normExponent_eq {C L : ℝ} (hl : log L ≠ 0) :
    normExponent C L = sqrt (2 * L) *
      (1 / log L + (2 + log 2) / log L ^ 2 - C / log L ^ 3) := by
  unfold normExponent widthExponent secondScale
  field_simp
  ring

/-- Expansion of the reciprocals at `log z = log L - log 2`, with an explicit
bound on the effect of the third-order term. -/
theorem shiftedLog_lower {l k C : ℝ} (hl : 0 < l) (hk : 0 ≤ k)
    (hkl : 2 * k ≤ l) (hC : 0 ≤ C) :
    (1 + (2 + k) / l - 8 * C / l ^ 2) / l ≤
      (1 + 2 / (l - k) - C / (l - k) ^ 2) / (l - k) := by
  have hden : 0 < l - k := by linarith
  have h₁ : 1 / l + k / l ^ 2 ≤ 1 / (l-k) := by
    field_simp
    nlinarith [sq_nonneg k]
  have h₂ : 2 / l ^ 2 ≤ 2 / (l-k) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hden)
      (pow_le_pow_left₀ hden.le (by linarith) _)
  have h₃ : C / (l-k) ^ 3 ≤ 8 * C / l ^ 3 := by
    have hcubed := pow_le_pow_left₀ hl.le (show l ≤ 2 * (l-k) by linarith) 3
    have h := mul_le_mul_of_nonneg_left hcubed hC
    field_simp
    nlinarith
  calc
    _ = (1 / l + k / l ^ 2) + 2 / l ^ 2 - 8 * C / l ^ 3 := by ring
    _ ≤ 1 / (l-k) + 2 / (l-k) ^ 2 - C / (l-k) ^ 3 := by linarith
    _ = _ := by field_simp

/-- Replacing the prime cutoff by half the logarithm of the long variable
retains the coefficient `2 + log 2`. The input bounds allow the logarithmic
cutoff to move by at most `1/log L` and the square-root factor by a relative
`1/(log L)^2`. -/
theorem normExponent_le_cutoff {C L z : ℝ} (hC : 0 ≤ C) (hl : 1 ≤ log L)
    (hk : 0 ≤ log 2 - 1 / log L)
    (hz₁ : log L / 2 ≤ log z) (hz₂ : log z ≤ log L - log 2 + 1 / log L)
    (hCz : C ≤ log z ^ 2)
    (hroot : sqrt (2 * L) * (1 - 1 / log L ^ 2) ≤ 2 * sqrt z) :
    normExponent (8*C + 4 + log 2) L ≤
      2 * sqrt z * (1 / log z + 2 / log z ^ 2 - C / log z ^ 3) := by
  let l := log L
  let x := log z
  let k := log 2
  have hl₀ : 0 < l := by linarith [hl]
  have hx₀ : 0 < x := by linarith [hz₁]
  have hk₀ : 0 ≤ k := Real.log_nonneg (by norm_num)
  let y := l - (k - 1 / l)
  have hxy : x ≤ y := by dsimp [x, y, l, k]; linarith
  have hy : 0 < y := hx₀.trans_le hxy
  have hpk : 2 * (k - 1/l) ≤ l := by
    dsimp [y] at hxy
    linarith [show l/2 ≤ x from hz₁]
  have hfirst : 1/l + (2+k)/l^2 - 1/l^3 ≤ 1/x + 2/x^2 := by
    calc
      _ = (1 + (2 + (k - 1/l))/l) / l := by field_simp; ring
      _ ≤ (1 + 2/y) / y := by
        simpa [y] using (shiftedLog_lower hl₀ hk hpk (C := 0) le_rfl)
      _ = 1/y + 2/y^2 := by field_simp
      _ ≤ _ := add_le_add (div_le_div_of_nonneg_left (by norm_num) hx₀ hxy)
        (div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hx₀)
          (pow_le_pow_left₀ hx₀.le hxy 2))
  have herr : C/x^3 ≤ 8*C/l^3 := by
    have hh := pow_le_pow_left₀ hl₀.le (show l ≤ 2*x by linarith [hz₁]) 3
    have := mul_le_mul_of_nonneg_left hh hC
    field_simp
    nlinarith
  let B := 1/l + (2+k)/l^2 - (1+8*C)/l^3
  let G := 1/x + 2/x^2 - C/x^3
  have hG : B ≤ G := by
    calc
      B = (1/l + (2+k)/l^2 - 1/l^3) - (8*C/l^3) := by dsimp [B]; ring
      _ ≤ G := sub_le_sub hfirst herr
  have hG₀ : 0 ≤ G := by
    have hh : C/x^3 ≤ 1/x := by
      field_simp
      nlinarith [mul_le_mul_of_nonneg_right hCz hx₀.le]
    dsimp [G]
    linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg x)]
  have hl₁ : 1 ≤ l := hl
  have hB : B ≤ (3+k)/l := by
    have hh : (2+k)/l^2 ≤ (2+k)/l :=
      div_le_div_of_nonneg_left (by linarith) hl₀ (by nlinarith)
    calc
      B ≤ 1/l + (2+k)/l^2 := sub_le_self _
        (div_nonneg (by linarith) (pow_nonneg hl₀.le 3))
      _ ≤ 1/l + (2+k)/l := add_le_add le_rfl hh
      _ = _ := by ring
  have hB' : B / l^2 ≤ (3+k)/l^3 := by
    convert div_le_div_of_nonneg_right hB (sq_nonneg l) using 1
    ring
  have hcoef : 0 ≤ sqrt (2*L) * (1-1/l^2) := by
    apply mul_nonneg (sqrt_nonneg _)
    exact sub_nonneg.2 ((div_le_one (sq_pos_of_pos hl₀)).2 (by nlinarith))
  rw [normExponent_eq hl₀.ne']
  calc
    _ = sqrt (2*L) * (B - (3+k)/l^3) := by dsimp [B, l, k]; ring
    _ ≤ sqrt (2*L) * (B - B/l^2) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hB' _) (sqrt_nonneg _)
    _ = (sqrt (2*L) * (1-1/l^2))*B := by ring
    _ ≤ (sqrt (2*L) * (1-1/l^2))*G := mul_le_mul_of_nonneg_left hG hcoef
    _ ≤ _ := mul_le_mul_of_nonneg_right hroot hG₀

/-- The permitted error in selecting the primorial cutoff in (8) is small
enough for the second-order expansion. Here `A` is the constant in that
cutoff estimate and `C` is the constant in the sieve's third-order error. -/
theorem eventually_normExponent_le_of_cutoff {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ z : ℝ, |z-L/2| ≤ A * sqrt L * log L ^ 2 →
      normExponent (8*C + 4 + log 2) L ≤
        2 * sqrt z * (1 / log z + 2 / log z^2 - C / log z^3) := by
  have ho : (fun L : ℝ => log L ^ (4 : ℕ)) =o[atTop] (fun L => sqrt L) := by
    simpa [Real.rpow_natCast, Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (s := 1 / 2) 4 (by norm_num))
  have hl2 : 0 < log 2 := by positivity
  let K := 4 * (A + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  let M := max 1 (max (1/log 2) (max (2*log 4) (2*sqrt C)))
  filter_upwards [ho.bound (inv_pos.2 hK), Real.tendsto_log_atTop.eventually_ge_atTop M,
    eventually_ge_atTop (2 : ℝ)] with L hsmall hlog hL
  intro z hz
  let l := log L
  have hl₁ : 1 ≤ l := (le_max_left _ _).trans hlog
  have hl : 0 < l := by linarith
  have hL₀ : 0 < L := by linarith
  rw [Real.norm_of_nonneg (pow_nonneg hl.le _), Real.norm_of_nonneg (sqrt_nonneg _),
    inv_mul_eq_div, le_div_iff₀ hK] at hsmall
  have hsmall' : 4*A*l^4 ≤ sqrt L := by
    dsimp [K] at hsmall
    nlinarith [pow_nonneg hl.le 4]
  have hdev : |z-L/2| ≤ L/(4*l^2) := by
    refine hz.trans ((le_div_iff₀ (by positivity)).2 ?_)
    have hh := mul_le_mul_of_nonneg_right hsmall' (sqrt_nonneg L)
    nlinarith [sq_sqrt hL₀.le]
  have hdev' : L/(4*l^2) ≤ L/4 :=
    div_le_div_of_nonneg_left hL₀.le (by norm_num) (by nlinarith)
  have hzlow : L/4 ≤ z := by linarith [(abs_le.1 hdev).1]
  have hz₀ : 0 < z := by linarith
  have h4 : 2*log 4 ≤ l := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans hlog))
  have hz₁ : l/2 ≤ log z := by
    have hh := Real.log_le_log (show 0 < L/4 by positivity) hzlow
    rw [Real.log_div hL₀.ne' (by norm_num)] at hh
    linarith
  have hz₂ : log z ≤ l - log 2 + 1/l := by
    have hh := Real.log_le_sub_one_of_pos (div_pos hz₀ (by positivity : 0 < L/2))
    rw [Real.log_div hz₀.ne' (by positivity), Real.log_div hL₀.ne' (by norm_num)] at hh
    have hj : z/(L/2) - 1 ≤ 1/l := by
      rw [show z/(L/2)-1 = (z-L/2)/(L/2) by field_simp]
      apply (div_le_iff₀ (by positivity : 0 < L/2)).2
      calc
        _ ≤ L/(4*l^2) := (abs_le.1 hdev).2
        _ ≤ _ := by
          have hh := div_le_div_of_nonneg_left hL₀.le (show 0 < 2*l by positivity)
            (show 2*l ≤ 4*l^2 by nlinarith)
          convert hh using 1
          ring
    linarith
  have hk : 0 ≤ log 2 - 1/l := by
    apply sub_nonneg.2
    have hm : 1/log 2 ≤ l := (le_max_left _ _).trans ((le_max_right _ _).trans hlog)
    exact (div_le_iff₀ hl).2 (by linarith [(div_le_iff₀ hl2).1 hm])
  have hzC : C ≤ log z^2 := by
    have h₁ : 2 * sqrt C ≤ l := (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans hlog))
    have hsq := pow_le_pow_left₀ (sqrt_nonneg C) (show sqrt C ≤ log z by linarith) 2
    simpa only [sq_sqrt hC] using hsq
  have hroot : sqrt (2*L) * (1-1/l^2) ≤ 2*sqrt z := by
    have he₀ : 0 ≤ 1/l^2 := by positivity
    have he₁ : 1/l^2 ≤ 1 := (div_le_one (sq_pos_of_pos hl)).2 (by nlinarith)
    apply (sq_le_sq₀ (mul_nonneg (sqrt_nonneg _) (sub_nonneg.2 he₁)) (by positivity)).1
    rw [mul_pow, mul_pow, sq_sqrt (show 0 ≤ 2*L by positivity), sq_sqrt hz₀.le]
    have hsq : (1-1/l^2)^2 ≤ 1-1/l^2 := by
      nlinarith [mul_nonneg he₀ (sub_nonneg.2 he₁)]
    have hlow := (abs_le.1 hdev).1
    have hlower : 2*L * (1-1/l^2) ≤ 4*z := by
      rw [mul_sub, mul_one, mul_one_div]
      have hh : 2*L / l^2 = 8 * (L/(4*l^2)) := by ring
      rw [hh]
      linarith [div_nonneg hL₀.le (by positivity : 0 ≤ 4*l^2)]
    simpa only [show (2 : ℝ)^2 = 4 by norm_num] using
      (mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2*L)).trans hlower
  exact normExponent_le_cutoff hC hl₁ hk hz₁ hz₂ hzC hroot

theorem eventually_log_le_secondScale {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, log L ≤ c * secondScale L := by
  have ho : (fun L : ℝ => log L ^ (3 : ℕ)) =o[atTop] (fun L => sqrt L) := by
    simpa [Real.rpow_natCast, Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (s := 1 / 2) 3 (by norm_num))
  filter_upwards [ho.bound hc, eventually_ge_atTop (2 : ℝ)] with L hL hL₂
  have hL₀ : 0 ≤ L := by linarith
  have hl : 0 < log L := log_pos (by linarith)
  have hs := sqrt_le_sqrt (show L ≤ 2 * L by linarith)
  change ‖log L ^ (3 : ℕ)‖ ≤ c * ‖sqrt L‖ at hL
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (sqrt_nonneg _)] at hL
  unfold secondScale
  rw [← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos hl)]
  calc
    log L * log L ^ 2 = log L ^ 3 := by ring
    _ ≤ c * sqrt L := hL
    _ ≤ c * sqrt (2 * L) := mul_le_mul_of_nonneg_left hs hc.le

theorem eventually_widthExponent_large {a : ℝ} (ha : 0 < a) (d A B : ℝ) :
    ∀ᶠ L : ℝ in atTop, A * log L + B < widthExponent a d L := by
  let K : ℝ := |A| + |B| + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have ht := Real.tendsto_log_atTop.eventually_ge_atTop (max 1 ((1-d)/a))
  filter_upwards [eventually_log_le_secondScale (inv_pos.mpr hK), ht] with L h hlog
  have hlog₁ : 1 ≤ log L := (le_max_left _ _).trans hlog
  have hcoef : 1 ≤ a * log L + d := by
    have hh := (div_le_iff₀ ha).1 ((le_max_right _ _).trans hlog)
    linarith
  have hscale : K * log L ≤ secondScale L := by
    rwa [inv_mul_eq_div, le_div_iff₀ hK, mul_comm] at h
  have hpos := secondScale_nonneg L
  have hA := mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith : 0 ≤ log L)
  have hB := mul_le_mul_of_nonneg_left hlog₁ (abs_nonneg B)
  calc
    A * log L + B < K * log L := by dsimp [K]; nlinarith [le_abs_self B]
    _ ≤ secondScale L := hscale
    _ ≤ widthExponent a d L := by
      unfold widthExponent
      simpa using mul_le_mul_of_nonneg_right hcoef hpos

theorem eventually_widthExponent_le_quarter {a : ℝ} (ha : 0 ≤ a) (d : ℝ) :
    ∀ᶠ L : ℝ in atTop, widthExponent a d L ≤ L / 4 := by
  let K := a + |d|
  have hK : 0 ≤ K := add_nonneg ha (abs_nonneg d)
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (32 * K ^ 2)] with L hl hL
  have hL₀ : 0 ≤ L := le_trans (by positivity) hL
  have hls : 1 ≤ log L ^ 2 := by nlinarith
  have hlog : log L ≤ log L ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hl) (show 0 ≤ log L by linarith)]
  have hh : a * log L + d ≤ K * log L ^ 2 := by
    dsimp [K]
    nlinarith [mul_le_mul_of_nonneg_left hlog ha,
      mul_le_mul_of_nonneg_left hls (abs_nonneg d), le_abs_self d]
  have hs : 8 * K ≤ sqrt (2 * L) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 8 * K)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  unfold widthExponent secondScale
  calc
    _ ≤ (K * log L ^ 2) * (sqrt (2 * L) / log L ^ 2) :=
      mul_le_mul_of_nonneg_right hh (by positivity)
    _ = K * sqrt (2 * L) := by
      have : log L ≠ 0 := by linarith
      field_simp
    _ ≤ L / 4 := by
      nlinarith [mul_le_mul_of_nonneg_right hs (sqrt_nonneg (2 * L)),
        sq_sqrt (show 0 ≤ 2 * L by linarith)]

/-- The strictly positive second-order margin dominates all logarithmic losses.
In particular this includes `a = 1, d = 0`, the endpoint of the first family. -/
theorem eventually_normExponent_gap {a d : ℝ} (ha : a ≤ 1) (hd : d < 2 + log 2)
    (C A B : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      A * log L + B < normExponent C L - widthExponent a d L := by
  let δ := (2 + log 2 - d) / 2
  let K := |A| + |B| + 1
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hK : 0 < K := by dsimp [K]; positivity
  filter_upwards [eventually_log_le_secondScale (div_pos hδ hK),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (|C| / δ))] with L h hl
  have hl₁ : 1 ≤ log L := (le_max_left _ _).trans hl
  have hl₀ : 0 < log L := by linarith
  have hC : C / log L ≤ δ := by
    apply (div_le_iff₀ hl₀).2
    have h := (div_le_iff₀ hδ).1 ((le_max_right _ _).trans hl)
    linarith [le_abs_self C]
  have hcoef : δ ≤ (1 - a) * log L + (2 + log 2 - d) - C / log L := by
    dsimp [δ] at *
    linarith [mul_nonneg (sub_nonneg.2 ha) hl₀.le]
  have hL : K * log L ≤ δ * secondScale L := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hK] at h
    simpa [mul_comm] using h
  calc
    A * log L + B < K * log L := by
      have hA := mul_le_mul_of_nonneg_right (le_abs_self A) hl₀.le
      have hB := mul_le_mul_of_nonneg_left hl₁ (abs_nonneg B)
      dsimp [K]
      nlinarith [le_abs_self B]
    _ ≤ δ * secondScale L := hL
    _ ≤ _ := by
      unfold normExponent widthExponent
      convert mul_le_mul_of_nonneg_right hcoef (secondScale_nonneg L) using 1
      ring

end

end

end PrescribedSWidth
