import Mathlib
import Submission.Work.Mostow.KMdefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.pairStabDefs
import Submission.Work.Mostow.horoball_minkowski_pair
import Submission.Work.Mostow.busemannCocycle
import Submission.Work.Mostow.HLlinks
import Submission.Work.Mostow.mformSqLeTheta
import Submission.Work.Mostow.mformPosTheta
import Submission.Work.Mostow.perpNullUnit
import Submission.Work.Mostow.coreIneq
import Submission.Work.Mostow.coreIneqZero

/-!
# `Work.Mostow.rayStrictPair` — the strict-pair ray lemma (KM-E(ii))

For two distinct boundary points `a ≠ b` of `ℍⁿ` (`n ≥ 2`) and any point `x`, every isometry
`g : PO n 1` preserving the unordered pair `{a,b}` which moves `x` at all moves a suitable point
`x'` arbitrarily close to `x` strictly further: `hdist x (g • x) < hdist x' (g • x')`.

The mechanism is the orthogonal decomposition of the chart lift `u = hlift x` with respect to the
plane `V = span{θ a, θ b}` (`θ ξ = (ξ,1)` is the null lift of a boundary point):

  `u = pp + cc`,   `pp ∈ V`,  `cc ∈ V^⊥ = {z | ⟨z,θ a⟩ = ⟨z,θ b⟩ = 0}`,

where `pp = (2/dd) • (lb • θ a + la • θ b)`, `la = lev a x`, `lb = lev b x`,
`dd = 2 (1 - ⟨a,b⟩)` and `cc = u - pp`.  Writing `PP = -⟨pp,pp⟩ = 1 + CC`, `CC = ⟨cc,cc⟩ ≥ 0`,
every `M = emat g` with `g` preserving the pair `{a,b}` maps `V` to itself, hence `V^⊥` to itself,
and pairs `u = pp + cc` with its image as `-A + B` where `A = -⟨pp, M pp⟩`, `B = ⟨cc, M cc⟩ ≤ CC`.
Increasing the `V^⊥`-component of `u` strictly decreases `⟨u, Mu⟩`, i.e. strictly increases the
displacement: this is the content of `coreIneq` / `coreIneqZero`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Matrix

set_option maxHeartbeats 6000000
set_option linter.unusedVariables false

variable {n : ℕ}

/-! ## Elementary Minkowski and chart lemmas -/

/-- The Minkowski pairing of two hyperboloid lifts is at most `-1`. -/
lemma rayStrictMformLe (x y : E n) : mform (hlift x) (hlift y) ≤ -1 := by
  rw [mform_hlift_hlift]
  have hx0 : (0 : ℝ) ≤ 1 + ‖x‖ ^ 2 := by positivity
  have h1 : tpart x * tpart y = Real.sqrt ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2)) := by
    rw [tpart, tpart, ← Real.sqrt_mul hx0 (1 + ‖y‖ ^ 2)]
  rw [h1]
  have h2 : 1 + ‖x‖ * ‖y‖ ≤ Real.sqrt ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2)) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 + ‖x‖ * ‖y‖)]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  have h3 : inner ℝ x y ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
  linarith

/-- Homogeneity of `mform` of degree two. -/
lemma rayStrictMformSelf (c : ℝ) (β : Fin n ⊕ Fin 1 → ℝ) :
    mform (c • β) (c • β) = c ^ 2 * mform β β := by
  rw [mform_smul_left, mform_smul_right]; ring

/-- Bilinear expansion of `mform` in a two-dimensional span. -/
lemma rayStrictMformComb (r s r' s' : ℝ) (β γ : Fin n ⊕ Fin 1 → ℝ) :
    mform (r • β + s • γ) (r' • β + s' • γ)
      = r * r' * mform β β + r * s' * mform β γ + s * r' * mform γ β + s * s' * mform γ γ := by
  simp only [mform_add_left, mform_add_right, mform_smul_left, mform_smul_right]
  ring

/-- Bilinear expansion of `mform` in the first variable. -/
lemma rayStrictMformCombRight (r s : ℝ) (β γ X : Fin n ⊕ Fin 1 → ℝ) :
    mform (r • β + s • γ) X = r * mform β X + s * mform γ X := by
  simp only [mform_add_left, mform_smul_left]

/-- A vector in `span{θ a, θ b}` pairs to zero with a vector orthogonal to both. -/
lemma rayStrictCrossLeft {a b : E n} {u X : Fin n ⊕ Fin 1 → ℝ}
    (huV : ∃ r s : ℝ, u = r • theta a + s • theta b)
    (hX : mform X (theta a) = 0 ∧ mform X (theta b) = 0) : mform u X = 0 := by
  obtain ⟨r, s, rfl⟩ := huV
  rw [mform_add_left, mform_smul_left, mform_smul_left, mform_comm (theta a) X,
    mform_comm (theta b) X, hX.1, hX.2, mul_zero, mul_zero, add_zero]

/-- A vector orthogonal to both `θ a, θ b` pairs to zero with a vector in `span{θ a, θ b}`. -/
lemma rayStrictCrossRight {a b : E n} {cc X : Fin n ⊕ Fin 1 → ℝ}
    (hcc : mform cc (theta a) = 0 ∧ mform cc (theta b) = 0)
    (hX : ∃ r s : ℝ, X = r • theta a + s • theta b) : mform cc X = 0 := by
  obtain ⟨r, s, rfl⟩ := hX
  rw [mform_add_right, mform_smul_right, mform_smul_right, hcc.1, hcc.2, mul_zero, mul_zero,
    add_zero]

/-- `hdist` in Minkowski form. -/
lemma rayStrictHdistEq (x y : E n) :
    hdist x y = Real.arcosh (-(mform (hlift x) (hlift y))) := by
  rw [hdist_eq_arcosh_mink, mink_eq_mform]

/-- `hdist x (g • x)` in terms of `emat g`. -/
lemma rayStrictHdistSmul (x : E n) (g : PO n 1) :
    hdist x (g • x) = Real.arcosh (-(mform (hlift x) ((emat g) *ᵥ (hlift x)))) := by
  rw [rayStrictHdistEq, emat_hlift]

/-- Moving `x` (at all) is equivalent to `⟨hlift x, emat g (hlift x)⟩ < -1`. -/
lemma rayStrictHdistPos {x : E n} {g : PO n 1} :
    0 < hdist x (g • x) ↔ mform (hlift x) ((emat g) *ᵥ (hlift x)) < -1 := by
  have hge : 1 ≤ -(mform (hlift x) ((emat g) *ᵥ (hlift x))) := by
    have h := rayStrictMformLe x (g • x)
    rw [← emat_hlift] at h
    linarith
  rw [rayStrictHdistSmul]
  constructor
  · intro h
    have h' : 1 < Real.cosh (Real.arcosh (-(mform (hlift x) ((emat g) *ᵥ (hlift x))))) :=
      Real.one_lt_cosh.mpr (ne_of_gt h)
    rw [Real.cosh_arcosh hge] at h'
    linarith
  · intro h
    have h' : 1 < Real.cosh (Real.arcosh (-(mform (hlift x) ((emat g) *ᵥ (hlift x))))) := by
      rw [Real.cosh_arcosh hge]; linarith
    have hne : Real.arcosh (-(mform (hlift x) ((emat g) *ᵥ (hlift x)))) ≠ 0 :=
      Real.one_lt_cosh.mp h'
    have hnn : 0 ≤ Real.arcosh (-(mform (hlift x) ((emat g) *ᵥ (hlift x)))) :=
      Real.arcosh_nonneg hge
    exact lt_of_le_of_ne hnn (Ne.symm hne)

/-- A vector with `mform z z = 0` and `⟨z, θ a⟩ = 0` is a multiple of `θ a`. -/
lemma rayStrictSmulTheta {a : E n} (ha : a ∈ Sph n) {z : Fin n ⊕ Fin 1 → ℝ}
    (hza : mform z (theta a) = 0) (hz : mform z z = 0) : z = htime z • theta a := by
  have hna : ‖a‖ = 1 := (mem_Sph_iff a).1 ha
  have h1 : htime z = inner ℝ (hspat z) a := by
    have h := hza
    rw [mform_eq, hspat_theta, htime_theta, mul_one] at h
    linarith
  have h4 : mform z z = ‖hspat z‖ ^ 2 - htime z ^ 2 := by
    rw [mform_eq, real_inner_self_eq_norm_sq]; ring
  have h3 : ‖hspat z - htime z • a‖ ^ 2 = ‖hspat z‖ ^ 2 - htime z ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, h1, norm_smul, hna, mul_one, Real.norm_eq_abs,
      sq_abs]
    ring
  have h5 : hspat z - htime z • a = 0 := by
    have h := h3
    rw [← h4, hz] at h
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)
  have h5' : hspat z = htime z • a := sub_eq_zero.mp h5
  conv_lhs => rw [eq_elim_hspat_htime z]
  ext k
  rcases k with i | j
  · have h := congrArg (fun v : E n => v i) h5'
    simpa [Pi.smul_apply, smul_eq_mul, theta_inl] using h
  · obtain rfl : j = 0 := Subsingleton.elim j 0
    simp [htime, theta]

/-- A vector orthogonal to `θ a` and `θ b` with vanishing Minkowski square is zero. -/
lemma rayStrictEqZero {a b : E n} (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    {z : Fin n ⊕ Fin 1 → ℝ} (hza : mform z (theta a) = 0) (hzb : mform z (theta b) = 0)
    (hz : mform z z = 0) : z = 0 := by
  have hsm := rayStrictSmulTheta ha hza hz
  have hθ : mform (theta a) (theta b) ≠ 0 := by
    rw [mform_theta_theta_pair]
    have h1 : inner ℝ a b < 1 :=
      inner_lt_one_of_ne_unit ((mem_Sph_iff a).1 ha) ((mem_Sph_iff b).1 hb) hab
    intro h; linarith
  have h2 : htime z * mform (theta a) (theta b) = 0 := by
    have h := hzb
    rw [hsm, mform_smul_left] at h
    exact h
  have htz : htime z = 0 := (mul_eq_zero.mp h2).resolve_right hθ
  rw [hsm, htz, zero_smul]

/-- Cauchy–Schwarz on `{z | ⟨z, θ a⟩ = 0}` bounds the pairing with an `mform`-preserving image. -/
lemma rayStrictCS {g : PO n 1} {a : E n} (ha : a ∈ Sph n) {v : Fin n ⊕ Fin 1 → ℝ} {C : ℝ}
    (hv : mform v (theta a) = 0) (hMv : mform ((emat g) *ᵥ v) (theta a) = 0)
    (hvv : mform v v = C) (hMM : mform ((emat g) *ᵥ v) ((emat g) *ᵥ v) = C) (hC : 0 ≤ C) :
    mform v ((emat g) *ᵥ v) ≤ C := by
  have hcs := mformSqLeTheta ha hv hMv
  rw [hvv, hMM] at hcs
  by_contra hcon
  push_neg at hcon
  have hxpos : 0 < mform v ((emat g) *ᵥ v) := lt_of_le_of_lt hC hcon
  have h1 : C * C ≤ mform v ((emat g) *ᵥ v) * C := mul_le_mul_of_nonneg_right hcon.le hC
  have h2 : mform v ((emat g) *ᵥ v) * C < mform v ((emat g) *ᵥ v) * mform v ((emat g) *ᵥ v) :=
    mul_lt_mul_of_pos_left hcon hxpos
  nlinarith [hcs, h1, h2]

/-- The Minkowski pairing of the image under an eigen-direction map. -/
lemma rayStrictMvPerp {M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ} {x : Fin n ⊕ Fin 1 → ℝ}
    {ξ η : E n} {lam : ℝ}
    (hpres : ∀ x y, mform (M *ᵥ x) (M *ᵥ y) = mform x y)
    (hlam : lam ≠ 0) (heig : M *ᵥ (theta ξ) = lam • theta η) (hx : mform x (theta ξ) = 0) :
    mform (M *ᵥ x) (theta η) = 0 := by
  have h1 : mform (M *ᵥ x) (theta η) * lam = mform (M *ᵥ x) (M *ᵥ (theta ξ)) := by
    rw [heig, mform_smul_right]; ring
  rw [hpres, hx] at h1
  exact (mul_eq_zero.mp h1).resolve_right hlam

/-- `emat g` preserves `V^⊥ = {z | ⟨z,θ a⟩ = ⟨z,θ b⟩ = 0}` when `g` preserves the pair `{a,b}`,
and the cross pairings with `span{θ a, θ b}` vanish. -/
lemma rayStrictPerp {g : PO n 1} {a b : E n} (ha : a ∈ Sph n) (hb : b ∈ Sph n)
    (hfam : (bd g a = a ∧ bd g b = b) ∨ (bd g a = b ∧ bd g b = a))
    {pp cc : Fin n ⊕ Fin 1 → ℝ}
    (hppV : ∃ r s : ℝ, pp = r • theta a + s • theta b)
    (hccV : mform cc (theta a) = 0 ∧ mform cc (theta b) = 0) :
    (mform ((emat g) *ᵥ cc) (theta a) = 0 ∧ mform ((emat g) *ᵥ cc) (theta b) = 0) ∧
    mform pp ((emat g) *ᵥ cc) = 0 ∧ mform cc ((emat g) *ᵥ pp) = 0 := by
  have hpres : ∀ x y, mform ((emat g) *ᵥ x) ((emat g) *ᵥ y) = mform x y :=
    fun x y => mform_emat g x y
  have hperp : mform ((emat g) *ᵥ cc) (theta a) = 0 ∧ mform ((emat g) *ᵥ cc) (theta b) = 0 := by
    rcases hfam with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨lam, hlamne, hlam⟩ := bd_emat_eigen ha h1
      obtain ⟨mu, hmune, hmu⟩ := bd_emat_eigen hb h2
      exact ⟨rayStrictMvPerp hpres hlamne hlam hccV.1,
             rayStrictMvPerp hpres hmune hmu hccV.2⟩
    · obtain ⟨lam, hlamne, hlam⟩ := bd_emat_eigen ha h1
      obtain ⟨mu, hmune, hmu⟩ := bd_emat_eigen hb h2
      exact ⟨rayStrictMvPerp hpres hmune hmu hccV.2,
             rayStrictMvPerp hpres hlamne hlam hccV.1⟩
  have hMppV : ∃ r s : ℝ, (emat g) *ᵥ pp = r • theta a + s • theta b := by
    obtain ⟨r, s, hrs⟩ := hppV
    rw [hrs, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    rcases hfam with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨lam, hlamne, hlam⟩ := bd_emat_eigen ha h1
      obtain ⟨mu, hmune, hmu⟩ := bd_emat_eigen hb h2
      exact ⟨r * lam, s * mu, by rw [hlam, hmu]; module⟩
    · obtain ⟨lam, hlamne, hlam⟩ := bd_emat_eigen ha h1
      obtain ⟨mu, hmune, hmu⟩ := bd_emat_eigen hb h2
      exact ⟨s * mu, r * lam, by rw [hlam, hmu]; module⟩
  exact ⟨hperp, rayStrictCrossLeft hppV hperp, rayStrictCrossRight hccV hMppV⟩

/-- Existence of a small positive parameter below a positive constant. -/
lemma rayStrictExistsDelta {c : ℝ} (hc : 0 < c) : ∃ d : ℝ, 0 < d ∧ d < c ∧ d < 1 := by
  refine ⟨min c 1 / 2, ?_, ?_, ?_⟩
  · have h : 0 < min c 1 := lt_min hc one_pos
    linarith
  · have h : min c 1 ≤ c := min_le_left c 1
    linarith
  · have h : min c 1 ≤ 1 := min_le_right c 1
    linarith

/-- `1 / √(1 - Q) ≤ 1 + Q` for `Q ∈ [0, 1/2]`. -/
lemma rayStrictOneDivSqrtLe {Q : ℝ} (h0 : 0 ≤ Q) (hQ : Q ≤ 1 / 2) :
    1 / Real.sqrt (1 - Q) ≤ 1 + Q := by
  have h1Q : 0 < 1 - Q := by linarith
  have hs : 0 < Real.sqrt (1 - Q) := Real.sqrt_pos.mpr h1Q
  have hsq : (1 : ℝ) ^ 2 ≤ ((1 + Q) * Real.sqrt (1 - Q)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt h1Q)]
    have hfac : 0 ≤ Q * (1 - Q - Q * Q) := by
      apply mul_nonneg h0
      nlinarith
    nlinarith [hfac]
  have hpos : (0 : ℝ) ≤ (1 + Q) * Real.sqrt (1 - Q) := by positivity
  have h3 : (1 : ℝ) ≤ (1 + Q) * Real.sqrt (1 - Q) := by
    have h := sq_le_sq.mp hsq
    rwa [abs_one, abs_of_nonneg hpos] at h
  rw [div_le_iff₀ hs]
  exact h3

/-! ## The main theorem -/

theorem rayStrictPair (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (a b x : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) :
    ∀ τ : ℝ, 0 < τ → ∃ x' : E n, hdist x x' < τ ∧ ∀ g : PO n 1,
      ((bd g a = a ∧ bd g b = b) ∨ (bd g a = b ∧ bd g b = a)) → 0 < hdist x (g • x) →
      hdist x (g • x) < hdist x' (g • x') := by
  intro τ hτ
  have ha1 : ‖a‖ = 1 := (mem_Sph_iff a).1 ha
  have hb1 : ‖b‖ = 1 := (mem_Sph_iff b).1 hb
  have hcosh : 0 < Real.cosh τ - 1 := by
    have h := Real.one_lt_cosh.mpr (ne_of_gt hτ); linarith
  -- ## The decomposition `u = pp + cc`
  set dd : ℝ := 2 * (1 - inner ℝ a b) with hdd
  have hddpos : 0 < dd := by
    rw [hdd]; have := inner_lt_one_of_ne_unit ha1 hb1 hab; linarith
  have hddne : dd ≠ 0 := ne_of_gt hddpos
  have hmth : mform (theta a) (theta b) = -(dd / 2) := by
    rw [mform_theta_theta_pair, hdd]; ring
  have hmth' : mform (theta b) (theta a) = -(dd / 2) := by rw [mform_comm]; exact hmth
  set la : ℝ := lev a x with hla
  set lb : ℝ := lev b x with hlb
  have hlapos : 0 < la := by rw [hla]; exact lev_pos a ha x
  have hlbpos : 0 < lb := by rw [hlb]; exact lev_pos b hb x
  set u : Fin n ⊕ Fin 1 → ℝ := hlift x with hu
  have hu_self : mform u u = -1 := by rw [hu]; exact mform_hlift_self x
  set pp : Fin n ⊕ Fin 1 → ℝ := (2 / dd) • (lb • theta a + la • theta b) with hpp
  set cc : Fin n ⊕ Fin 1 → ℝ := u - pp with hcc
  set PP : ℝ := 4 * la * lb / dd with hPPdef
  set CC : ℝ := PP - 1 with hCCdef
  clear_value dd la lb u pp cc PP CC
  have hupc : u = pp + cc := by rw [hcc]; abel
  -- mform facts
  have hm_u_a : mform u (theta a) = -la := by
    rw [hu, hla, lev, mform_hlift_theta']; ring
  have hm_u_b : mform u (theta b) = -lb := by
    rw [hu, hlb, lev, mform_hlift_theta']; ring
  have hm_pp_a : mform pp (theta a) = -la := by
    rw [hpp, mform_smul_left, rayStrictMformCombRight, mform_theta_theta_sph a ha, hmth',
      hla, lev]
    field_simp
    ring
  have hm_pp_b : mform pp (theta b) = -lb := by
    rw [hpp, mform_smul_left, rayStrictMformCombRight, mform_theta_theta_sph b hb, hmth,
      hlb, lev]
    field_simp
    ring
  have hm_pp_u : mform pp u = -PP := by
    rw [hu, hpp, mform_smul_left, rayStrictMformCombRight, mform_comm (theta a) (hlift x),
      mform_comm (theta b) (hlift x), mform_hlift_theta', mform_hlift_theta', hPPdef,
      hla, hlb, lev, lev]
    field_simp
    ring
  have hm_pp_pp : mform pp pp = -PP := by
    rw [hpp, rayStrictMformSelf, rayStrictMformComb, mform_theta_theta_sph a ha,
      mform_theta_theta_sph b hb, hmth, hmth', hPPdef, hla, hlb, lev, lev]
    field_simp
    ring
  have hm_cc_a : mform cc (theta a) = 0 := by
    rw [hcc, mform_sub_left, hm_u_a, hm_pp_a]; ring
  have hm_cc_b : mform cc (theta b) = 0 := by
    rw [hcc, mform_sub_left, hm_u_b, hm_pp_b]; ring
  have hm_pp_cc : mform pp cc = 0 := by
    rw [hcc, mform_sub_right, hm_pp_u, hm_pp_pp]; ring
  have hm_cc_pp : mform cc pp = 0 := by rw [mform_comm]; exact hm_pp_cc
  have hm_cc_cc : mform cc cc = CC := by
    rw [hcc, mform_sub_left, mform_sub_right, mform_sub_right, mform_comm u pp, hu_self,
      hm_pp_u, hm_pp_pp, hCCdef]
    ring
  have hm_u_cc : mform u cc = CC := by
    rw [hupc, mform_add_left, hm_pp_cc, zero_add, hm_cc_cc]
  have hm_u_pp : mform u pp = -PP := by
    rw [hupc, mform_add_left, hm_pp_pp, hm_cc_pp, add_zero]
  have hPPCC : PP - CC = 1 := by rw [hCCdef]; ring
  have hPPrw : PP = 1 + CC := by linarith
  have hPPge1 : 1 ≤ PP := by
    have h := horoball_minkowski_pair n a b ha hb x
    rw [hPPdef, hla, hlb, hdd, lev, lev]
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * (1 - inner ℝ a b))]
    linarith
  have hCCnn : 0 ≤ CC := by rw [hCCdef]; linarith
  have hppV : ∃ r s : ℝ, pp = r • theta a + s • theta b :=
    ⟨2 / dd * lb, 2 / dd * la, by rw [hpp, smul_add, ← smul_smul, ← smul_smul]⟩
  -- ## The two cases
  by_cases hcz : cc = 0
  · -- ============ Case 1: `cc = 0` ============
    have hPP1 : PP = 1 := by
      have h := hm_cc_cc; rw [hcz, mform_zero_left] at h; linarith
    have hup : u = pp := by rw [hupc, hcz, add_zero]
    obtain ⟨w, hwa, hwb, hww⟩ := perpNullUnit hn ha hb hab
    -- the parameter
    set k : ℝ := min (min (1 / 2) (Real.cosh τ - 1)) (tpart x / (1 + |htime w|)) with hk
    have hkpos : 0 < k := by
      rw [hk]
      exact lt_min (lt_min (by norm_num) hcosh) (div_pos (tpart_pos x) (by positivity))
    obtain ⟨d, hdpos, hdk, hd1⟩ := rayStrictExistsDelta hkpos
    have hdk' : d < min (min (1 / 2) (Real.cosh τ - 1)) (tpart x / (1 + |htime w|)) := by
      rw [hk] at hdk; exact hdk
    have hdA : d < min (1 / 2) (Real.cosh τ - 1) := lt_of_lt_of_le hdk' (min_le_left _ _)
    have hdB : d < tpart x / (1 + |htime w|) := lt_of_lt_of_le hdk' (min_le_right _ _)
    have hdhalf : d < 1 / 2 := lt_of_lt_of_le hdA (min_le_left _ _)
    have hdcosh : d < Real.cosh τ - 1 := lt_of_lt_of_le hdA (min_le_right _ _)
    have hden : 0 < 1 - d ^ 2 := by nlinarith
    -- the perturbed vector
    set v : Fin n ⊕ Fin 1 → ℝ := u + d • w with hv
    clear_value k v
    have huV : ∃ r s : ℝ, u = r • theta a + s • theta b :=
      ⟨2 / dd * lb, 2 / dd * la, by rw [hup, hpp, smul_add, ← smul_smul, ← smul_smul]⟩
    have hu_w : mform u w = 0 := rayStrictCrossLeft huV ⟨hwa, hwb⟩
    have hw_u : mform w u = 0 := by rw [mform_comm]; exact hu_w
    have hvv : mform v v = -(1 - d ^ 2) := by
      simp only [hv, mform_add_left, mform_add_right, mform_smul_left, mform_smul_right,
        hu_self, hu_w, hw_u, hww, mul_zero, mul_one, zero_add, add_zero]
      ring
    set s : ℝ := Real.sqrt (1 - d ^ 2) with hs
    clear_value s
    have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hden
    have hs2 : s ^ 2 = 1 - d ^ 2 := by rw [hs, Real.sq_sqrt (le_of_lt hden)]
    have hu'_self : mform (s⁻¹ • v) (s⁻¹ • v) = -1 := by
      rw [mform_smul_left, mform_smul_right, hvv]
      field_simp
      nlinarith [hs2]
    have htimev : 0 < htime v := by
      have h1 : d * (1 + |htime w|) < tpart x :=
        (lt_div_iff₀ (by positivity : (0 : ℝ) < 1 + |htime w|)).mp hdB
      have hhint : d * (-htime w) ≤ d * |htime w| :=
        mul_le_mul_of_nonneg_left (neg_le_abs (htime w)) hdpos.le
      rw [hv, htime_add, htime_smul, hu, htime_hlift']
      nlinarith [h1, hhint]
    have hu'time : 0 < htime (s⁻¹ • v) := by
      rw [htime_smul]; exact mul_pos (inv_pos.mpr hspos) htimev
    have hliftx' : hlift (hspat (s⁻¹ • v)) = s⁻¹ • v :=
      (eq_hlift_of_upper _ hu'_self hu'time).symm
    refine ⟨hspat (s⁻¹ • v), ?hclose, ?hdisp⟩
    · -- closeness
      have hu_v : mform u v = -1 := by
        rw [hv, mform_add_right, mform_smul_right, hu_self, hu_w, mul_zero, add_zero]
      have hm_uu' : mform u (s⁻¹ • v) = -s⁻¹ := by
        rw [mform_smul_right, hu_v]; ring
      have hh : hdist x (hspat (s⁻¹ • v)) = Real.arcosh (s⁻¹) := by
        rw [rayStrictHdistEq, hliftx', ← hu, hm_uu']
        congr 1
        ring
      rw [hh, hs]
      have hs' : 0 < Real.sqrt (1 - d ^ 2) := Real.sqrt_pos.mpr hden
      have h2 := rayStrictOneDivSqrtLe (Q := d ^ 2) (by positivity) (by nlinarith)
      have h3 : (1 : ℝ) ≤ (1 + d ^ 2) * Real.sqrt (1 - d ^ 2) := by
        have h := mul_le_mul_of_nonneg_right h2 hs'.le
        rwa [one_div, inv_mul_cancel₀ (ne_of_gt hs')] at h
      have h4 : 1 + d ^ 2 < Real.cosh τ := by nlinarith
      have hbnd : (Real.sqrt (1 - d ^ 2))⁻¹ < Real.cosh τ := by
        have h5 : (1 + d ^ 2) * Real.sqrt (1 - d ^ 2) < Real.cosh τ * Real.sqrt (1 - d ^ 2) :=
          mul_lt_mul_of_pos_right h4 hs'
        have h6 : (1 : ℝ) < Real.cosh τ * Real.sqrt (1 - d ^ 2) := lt_of_le_of_lt h3 h5
        rw [← one_div, div_lt_iff₀ hs']
        exact h6
      have hfin : Real.arcosh ((Real.sqrt (1 - d ^ 2))⁻¹) < Real.arcosh (Real.cosh τ) :=
        (Real.arcosh_lt_arcosh (inv_pos.mpr hs') (Real.cosh_pos τ)).mpr hbnd
      rwa [Real.arcosh_cosh (le_of_lt hτ)] at hfin
    · -- the displacement comparison
      intro g hfam hpos
      have hmpos : mform u ((emat g) *ᵥ u) < -1 := by
        have h := rayStrictHdistPos.1 hpos
        rwa [← hu] at h
      obtain ⟨hperpW, hpMw, hwMp⟩ := rayStrictPerp ha hb hfam hppV ⟨hwa, hwb⟩
      have hB : mform w ((emat g) *ᵥ w) ≤ 1 :=
        rayStrictCS ha hwa hperpW.1 hww (by rw [mform_emat]; exact hww) (by norm_num)
      have hA : 1 < -mform pp ((emat g) *ᵥ pp) := by
        have h1 : mform pp ((emat g) *ᵥ pp) = mform u ((emat g) *ᵥ u) := by rw [hup]
        rw [h1]; linarith
      have hcore := coreIneqZero (emat g) pp w (-mform pp ((emat g) *ᵥ pp))
        (mform w ((emat g) *ᵥ w)) (by rw [← hup]; exact hu_w) hww hwMp hpMw (by ring) rfl hB hA
        d hdpos hd1
      have hlt : mform (s⁻¹ • v) ((emat g) *ᵥ (s⁻¹ • v)) < mform u ((emat g) *ᵥ u) := by
        rw [hv, hs, hup]
        exact hcore
      have h1 : mform (hlift x) (hlift (g • x)) = mform u ((emat g) *ᵥ u) := by
        rw [hu, emat_hlift]
      have h2 : mform (hlift (hspat (s⁻¹ • v))) (hlift (g • hspat (s⁻¹ • v)))
          = mform (s⁻¹ • v) ((emat g) *ᵥ (s⁻¹ • v)) := by
        rw [hliftx', ← emat_hlift, hliftx']
      have hge : 1 ≤ -(mform u ((emat g) *ᵥ u)) := by
        have h := rayStrictMformLe x (g • x); rw [h1] at h; linarith
      have hge2 : 1 ≤ -(mform (s⁻¹ • v) ((emat g) *ᵥ (s⁻¹ • v))) := by
        have h := rayStrictMformLe (hspat (s⁻¹ • v)) (g • hspat (s⁻¹ • v))
        rw [h2] at h
        linarith
      rw [rayStrictHdistEq, rayStrictHdistEq, h1, h2]
      exact (Real.arcosh_lt_arcosh (by linarith) (by linarith)).mpr (by linarith)
  · -- ============ Case 2: `cc ≠ 0` ============
    have hCCpos : 0 < CC := by
      rcases lt_or_eq_of_le hCCnn with h | h
      · exact h
      · exfalso
        exact hcz (rayStrictEqZero ha hb hab hm_cc_a hm_cc_b (by rw [hm_cc_cc, h]))
    have hPPtime : 0 < htime pp := by
      rw [hpp, htime_smul, htime_add, htime_smul, htime_smul, htime_theta, htime_theta]
      exact mul_pos (by positivity) (by linarith)
    set num : ℝ := min (1 / 2) (Real.cosh τ - 1) with hnum
    clear_value num
    have hnumpos : 0 < num := by rw [hnum]; exact lt_min (by norm_num) hcosh
    set k : ℝ := min (min 1 (1 / (3 * CC))) (min (tpart x / (1 + htime pp)) (num / (3 * CC)))
      with hk
    clear_value k
    have hk'pos1 : 0 < min 1 (1 / (3 * CC)) := lt_min one_pos (div_pos one_pos (by positivity))
    have hk'pos2 : 0 < min (tpart x / (1 + htime pp)) (num / (3 * CC)) :=
      lt_min (div_pos (tpart_pos x) (by linarith)) (div_pos hnumpos (by positivity))
    have hkpos : 0 < k := by rw [hk]; exact lt_min hk'pos1 hk'pos2
    obtain ⟨d, hdpos, hdk, hd1⟩ := rayStrictExistsDelta hkpos
    have hdk' : d < min (min 1 (1 / (3 * CC))) (min (tpart x / (1 + htime pp)) (num / (3 * CC))) := by
      rw [hk] at hdk; exact hdk
    have hd1' : d < min 1 (1 / (3 * CC)) := lt_of_lt_of_le hdk' (min_le_left _ _)
    have hd2' : d < min (tpart x / (1 + htime pp)) (num / (3 * CC)) :=
      lt_of_lt_of_le hdk' (min_le_right _ _)
    have hd3 : d < 1 / (3 * CC) := lt_of_lt_of_le hd1' (min_le_right _ _)
    have hdtp : d < tpart x / (1 + htime pp) := lt_of_lt_of_le hd2' (min_le_left _ _)
    have hdnum : d < num / (3 * CC) := lt_of_lt_of_le hd2' (min_le_right _ _)
    have h3dCC : 3 * d * CC < 1 := by
      have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < 3 * CC)).mp hd3
      linarith
    have h3dCCnum : 3 * d * CC < num := by
      have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < 3 * CC)).mp hdnum
      linarith
    have hdQ : d * (2 + d) * CC < 1 := by
      have hthis : d * (2 + d) < 3 * d := by nlinarith
      have h := mul_lt_mul_of_pos_right hthis hCCpos
      linarith
    have hdQnum : d * (2 + d) * CC < num := by
      have hthis : d * (2 + d) < 3 * d := by nlinarith
      have h := mul_lt_mul_of_pos_right hthis hCCpos
      linarith
    have hdQ1 : d * (2 + d) * CC < 1 / 2 := by
      have h := hdQnum
      rw [hnum] at h
      exact lt_of_lt_of_le h (min_le_left _ _)
    -- the perturbed vector
    set s : ℝ := Real.sqrt (PP - (1 + d) ^ 2 * CC) with hs
    set v : Fin n ⊕ Fin 1 → ℝ := pp + (1 + d) • cc with hv
    clear_value s v
    have hden : 0 < PP - (1 + d) ^ 2 * CC := by
      rw [hPPrw]; nlinarith
    have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hden
    have hs2 : s ^ 2 = PP - (1 + d) ^ 2 * CC := by rw [hs, Real.sq_sqrt (le_of_lt hden)]
    have hu'_self : mform (s⁻¹ • v) (s⁻¹ • v) = -1 := by
      have hvv : mform v v = -(PP - (1 + d) ^ 2 * CC) := by
        simp only [hv, mform_add_left, mform_add_right, mform_smul_left, mform_smul_right,
          hm_pp_pp, hm_cc_cc, hm_pp_cc, hm_cc_pp, mul_zero, zero_add]
        ring
      rw [mform_smul_left, mform_smul_right, hvv]
      field_simp
      nlinarith [hs2]
    have hu'time : 0 < htime (s⁻¹ • v) := by
      have hdHP : d * htime pp < tpart x := by
        have h := (lt_div_iff₀ (by linarith : (0 : ℝ) < 1 + htime pp)).mp hdtp
        have h2 : d * htime pp ≤ d * (1 + htime pp) :=
          mul_le_mul_of_nonneg_left (by linarith) hdpos.le
        linarith
      have htimecc : htime cc = tpart x - htime pp := by
        rw [hcc, htime_sub, hu, htime_hlift']
      have he1 : htime v = htime pp + (1 + d) * htime cc := by
        rw [hv, htime_add, htime_smul]
      have hv' : 0 < htime v := by
        rw [he1, htimecc]
        nlinarith only [hdHP, hdpos, tpart_pos x]
      rw [htime_smul]; exact mul_pos (inv_pos.mpr hspos) hv'
    have hliftx' : hlift (hspat (s⁻¹ • v)) = s⁻¹ • v :=
      (eq_hlift_of_upper _ hu'_self hu'time).symm
    refine ⟨hspat (s⁻¹ • v), ?hclose2, ?hdisp2⟩
    · -- closeness
      have hu_v : mform u v = d * CC - 1 := by
        rw [hv, mform_add_right, mform_smul_right, hm_u_pp, hm_u_cc, hPPrw]
        ring
      have hm_uu' : mform u (s⁻¹ • v) = (d * CC - 1) / s := by
        rw [mform_smul_right, hu_v, hs]
        ring
      have hh : hdist x (hspat (s⁻¹ • v)) = Real.arcosh ((1 - d * CC) / s) := by
        rw [rayStrictHdistEq, hliftx', ← hu, hm_uu']
        congr 1
        ring
      rw [hh]
      have hs_eq : s = Real.sqrt (1 - d * (2 + d) * CC) := by
        rw [hs, hPPrw]
        congr 1
        ring
      have hs'pos : 0 < Real.sqrt (1 - d * (2 + d) * CC) := Real.sqrt_pos.mpr (by linarith)
      have hmle : d * CC ≤ d * (2 + d) * CC := by
        have h2 : d * CC * (2 + d) = d * (2 + d) * CC := by ring
        calc d * CC ≤ d * CC * (2 + d) :=
              le_mul_of_one_le_right (mul_nonneg hdpos.le hCCnn) (by linarith)
          _ = d * (2 + d) * CC := h2
      have hdCClt : d * CC < 1 := lt_of_le_of_lt hmle (lt_of_lt_of_le hdQ1 (by norm_num))
      have hargpos : 0 < (1 - d * CC) / s := by
        rw [hs_eq]
        exact div_pos (sub_pos.mpr hdCClt) hs'pos
      have hbnd : (1 - d * CC) / s < Real.cosh τ := by
        rw [hs_eq]
        have h1 : (1 - d * CC) / Real.sqrt (1 - d * (2 + d) * CC)
            ≤ 1 / Real.sqrt (1 - d * (2 + d) * CC) := by
          rw [div_le_div_iff_of_pos_right hs'pos]
          linarith [mul_nonneg hdpos.le hCCnn]
        have h2 := rayStrictOneDivSqrtLe (Q := d * (2 + d) * CC) (by positivity)
          (le_of_lt hdQ1)
        have h3 : d * (2 + d) * CC < Real.cosh τ - 1 := by
          have h := hdQnum
          rw [hnum] at h
          exact lt_of_lt_of_le h (min_le_right _ _)
        linarith
      have hfin : Real.arcosh ((1 - d * CC) / s) < Real.arcosh (Real.cosh τ) :=
        (Real.arcosh_lt_arcosh hargpos (Real.cosh_pos τ)).mpr hbnd
      rwa [Real.arcosh_cosh (le_of_lt hτ)] at hfin
    · -- the displacement comparison
      intro g hfam hpos
      have hmpos : mform u ((emat g) *ᵥ u) < -1 := by
        have h := rayStrictHdistPos.1 hpos
        rwa [← hu] at h
      have hmu' : mform (pp + cc) ((emat g) *ᵥ (pp + cc)) < -1 := by
        rw [← hupc]; exact hmpos
      obtain ⟨hperp, hppMc, hccMp⟩ := rayStrictPerp ha hb hfam hppV ⟨hm_cc_a, hm_cc_b⟩
      have hB : mform cc ((emat g) *ᵥ cc) ≤ CC :=
        rayStrictCS ha hm_cc_a hperp.1 hm_cc_cc (by rw [mform_emat]; exact hm_cc_cc) hCCnn
      have hA : 1 < (-mform pp ((emat g) *ᵥ pp)) - mform cc ((emat g) *ᵥ cc) := by
        have h1 : mform (pp + cc) ((emat g) *ᵥ (pp + cc))
            = mform pp ((emat g) *ᵥ pp) + mform cc ((emat g) *ᵥ cc) := by
          simp only [Matrix.mulVec_add, mform_add_left, mform_add_right, hppMc, hccMp, add_zero,
            zero_add]
        rw [h1] at hmu'
        linarith
      have hcore := coreIneq (emat g) pp cc PP CC (-mform pp ((emat g) *ᵥ pp))
        (mform cc ((emat g) *ᵥ cc)) hm_pp_pp hm_cc_cc hm_pp_cc hPPCC hCCpos (by ring) rfl
        hppMc hccMp (by rw [mform_emat]; exact hm_cc_cc) hB hA d hdpos hden
      have hlt : mform (s⁻¹ • v) ((emat g) *ᵥ (s⁻¹ • v)) < mform u ((emat g) *ᵥ u) := by
        rw [hv, hs, hupc]
        exact hcore
      have h1 : mform (hlift x) (hlift (g • x)) = mform u ((emat g) *ᵥ u) := by
        rw [hu, emat_hlift]
      have h2 : mform (hlift (hspat (s⁻¹ • v))) (hlift (g • hspat (s⁻¹ • v)))
          = mform (s⁻¹ • v) ((emat g) *ᵥ (s⁻¹ • v)) := by
        rw [hliftx', ← emat_hlift, hliftx']
      have hge : 1 ≤ -(mform u ((emat g) *ᵥ u)) := by
        have h := rayStrictMformLe x (g • x); rw [h1] at h; linarith
      have hge2 : 1 ≤ -(mform (s⁻¹ • v) ((emat g) *ᵥ (s⁻¹ • v))) := by
        have h := rayStrictMformLe (hspat (s⁻¹ • v)) (g • hspat (s⁻¹ • v))
        rw [h2] at h
        linarith
      rw [rayStrictHdistEq, rayStrictHdistEq, h1, h2]
      exact (Real.arcosh_lt_arcosh (by linarith) (by linarith)).mpr (by linarith)

end Work.Mostow
