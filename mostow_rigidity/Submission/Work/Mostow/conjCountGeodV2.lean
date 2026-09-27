import Mathlib
import Submission.Work.Mostow.geodDeps
import Submission.Work.Mostow.nearId_blk
import Submission.Work.Mostow.zassenhausNilpotent
import Submission.Work.Mostow.finiteClosureNearIdAt
import Submission.Work.Mostow.frobeniusCommute
import Submission.Work.Mostow.boundedTorsionAux
import Submission.Work.Mostow.gapA.nilpotentPairNearIdAt

/-!
# `conjCountGeodV2`: conjugates of a block isometry with a small action

If `b = blk 1 m 1 R ∈ Λ` (with `R` fixing no nonzero vector) and both `b` and `g⁻¹ b g` act as
small isometries around a common point `w`, then `g` preserves the standard geodesic stratum
`stdTG 1 m`.

The proof follows the `n = 3` model `conjCount3`:

* `b` and `g⁻¹ b g` are torsion (they fix points, and `Λ` is discrete);
* being near-identity at `w` at scale `θ_Z`, the group they generate is nilpotent (Zassenhaus) and
  torsion-generated, hence finite;
* a finite subgroup of `PO (1+m) 1` fixes a point `p`; the two elements commute (Frobenius);
* both are near-identity at `p` at the Frobenius scale, obtained from the "two-scale" criterion
  `nearId_blk` for `b` (the conjugated element transports along `g`);
* the final geometric step: commuting with `b` makes `g⁻¹ b g` preserve the geodesic `Fix b`, on
  which it acts by an isometry with the fixed point `p`; a `ℍ¹`-isometry fixing a point is either
  the identity or the reflection about it, and the reflection is excluded by near-identity at scale
  `< 2`. Applying the same argument with the roles exchanged shows `Fix (g⁻¹ b g) = Fix b`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-! ## The one-dimensional model `E 1` of a geodesic -/

/-- the point of `E 1` with coordinate `x` -/
def e1 (x : ℝ) : E 1 := WithLp.toLp 2 (fun _ : Fin 1 => x)

lemma e1_apply (x : ℝ) (i : Fin 1) : e1 x i = x := rfl

lemma e1_ext (v : E 1) : e1 (v 0) = v := by
  ext i
  rw [e1_apply]
  have : i = 0 := Subsingleton.elim i 0
  rw [this]

lemma e1_injective : Function.Injective e1 := by
  intro a b hab
  have h : (fun _ : Fin 1 => a) = (fun _ : Fin 1 => b) := by
    simpa [e1] using congrArg WithLp.ofLp hab
  exact congrFun h 0

lemma inner_e1 (a b : ℝ) : inner ℝ (e1 a) (e1 b) = a * b := by
  rw [show e1 a = WithLp.toLp 2 (fun _ : Fin 1 => a) from rfl,
      show e1 b = WithLp.toLp 2 (fun _ : Fin 1 => b) from rfl]
  simp only [PiLp.inner_apply, Fin.sum_univ_one, RCLike.inner_apply, starRingEnd_apply,
    star_trivial]
  ring

lemma norm_e1_sq (a : ℝ) : ‖e1 a‖ ^ 2 = a ^ 2 := by
  rw [e1, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_one]

lemma tpart_e1 (a : ℝ) : tpart (e1 a) = Real.sqrt (1 + a ^ 2) := by
  rw [tpart, norm_e1_sq]

lemma cosh_hdist_e1_sinh (s t : ℝ) :
    Real.cosh (hdist (e1 (Real.sinh s)) (e1 (Real.sinh t))) = Real.cosh (s - t) := by
  rw [nib_cosh_hdist, tpart_e1, tpart_e1, inner_e1]
  have h1 : 1 + Real.sinh s ^ 2 = Real.cosh s ^ 2 := by rw [Real.cosh_sq]; ring
  have h2 : 1 + Real.sinh t ^ 2 = Real.cosh t ^ 2 := by rw [Real.cosh_sq]; ring
  rw [h1, h2, Real.sqrt_sq (le_of_lt (Real.cosh_pos s)), Real.sqrt_sq (le_of_lt (Real.cosh_pos t)),
      Real.cosh_sub]

/-- the arclength parametrisation of the geodesic `E 1`: distance `|s - t|`. -/
lemma hdist_e1_sinh (s t : ℝ) : hdist (e1 (Real.sinh s)) (e1 (Real.sinh t)) = |s - t| := by
  have h := cosh_hdist_e1_sinh s t
  have hle1 : |hdist (e1 (Real.sinh s)) (e1 (Real.sinh t))| ≤ |s - t| := by
    rw [← Real.cosh_le_cosh, h]
  have hle2 : |s - t| ≤ |hdist (e1 (Real.sinh s)) (e1 (Real.sinh t))| := by
    rw [← Real.cosh_le_cosh, ← h]
  have hEq : |hdist (e1 (Real.sinh s)) (e1 (Real.sinh t))| = |s - t| := le_antisymm hle1 hle2
  rwa [abs_of_nonneg (nib_hdist_nonneg _ _)] at hEq

/-! ## The geodesic `stdTG 1 m` as a copy of `E 1` -/

/-- the standard geodesic, parametrised by its Fermi coordinates -/
def phi (m : ℕ) (v : E 1) : E (1 + m) := fermiW 1 m v 0

/-- arclength parametrisation of `stdTG 1 m` -/
def arcGeo (m : ℕ) (t : ℝ) : E (1 + m) := phi m (e1 (Real.sinh t))

lemma arcGeo_arsinh (m : ℕ) (v : E 1) : arcGeo m (Real.arsinh (v 0)) = phi m v := by
  rw [arcGeo, Real.sinh_arsinh, e1_ext]

lemma range_arcGeo (m : ℕ) : Set.range (arcGeo m) = Set.range (phi m) := by
  apply le_antisymm
  · rintro u ⟨t, rfl⟩
    exact ⟨e1 (Real.sinh t), rfl⟩
  · rintro u ⟨v, rfl⟩
    exact ⟨Real.arsinh (v 0), arcGeo_arsinh m v⟩

lemma hdist_phi (m : ℕ) (v v' : E 1) : hdist (phi m v) (phi m v') = hdist v v' := by
  refine Real.cosh_injOn (nib_hdist_nonneg _ _) (nib_hdist_nonneg _ _) ?_
  simp only [phi]
  rw [nib_cosh_hdist_fermiW]
  simp

lemma hdist_arcGeo (m : ℕ) (s t : ℝ) : hdist (arcGeo m s) (arcGeo m t) = |s - t| := by
  simp only [arcGeo]
  rw [hdist_phi, hdist_e1_sinh]

lemma fermiW_zero_eq_coordEmb (m : ℕ) (v : E 1) : fermiW 1 m v 0 = coordEmb 1 m v := by
  rw [fermiW, coordEmb]
  congr 1
  ext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp
  · simp

lemma range_phi (m : ℕ) : Set.range (phi m) = stdTG 1 m := by
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    rw [stdTG, Set.mem_range]
    exact ⟨v, by rw [phi, fermiW_zero_eq_coordEmb]⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, by rw [phi, fermiW_zero_eq_coordEmb]; exact hv⟩
/-! ## The block isometry: fixed locus and small action on its axis -/

lemma blk_fixed_iff (m : ℕ) (hA1 : POActionProp 1) (hI1 : HypIsometryProp 1)
    (hA : POActionProp (1 + m)) (hI : HypIsometryProp (1 + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (hRnz : ∀ W : E m, R W = W → W = 0) (u : E (1 + m)) :
    (blk 1 m 1 R) • u = u ↔ nrmC 1 m u = 0 := by
  have hu' : fermiW 1 m ((Real.sqrt (1 + ‖nrmC 1 m u‖ ^ 2))⁻¹ • tanC 1 m u) (nrmC 1 m u) = u :=
    nib_fermiW_surj m u
  constructor
  · intro hu
    rw [← hu', nib_blk_smul_fermiW m hA1 hI1 hA hI R _ _] at hu
    have h1 : R (nrmC 1 m u) = nrmC 1 m u := by
      have := congrArg (fun x => nrmC 1 m x) hu
      simpa [nib_nrmC_fermiW] using this
    exact hRnz _ h1
  · intro hu
    rw [← hu']
    rw [nib_blk_smul_fermiW m hA1 hI1 hA hI R _ _, hu]
    simp

lemma nrmC_phi (m : ℕ) (v : E 1) : nrmC 1 m (phi m v) = 0 := by
  rw [phi]
  simp [nib_nrmC_fermiW]

lemma nrmC_eq_zero_iff (m : ℕ) (u : E (1 + m)) : nrmC 1 m u = 0 ↔ u ∈ Set.range (phi m) := by
  constructor
  · intro h
    refine ⟨tanC 1 m u, ?_⟩
    rw [phi]
    exact nib_eq_of_tanC_nrmC
      (by rw [nib_tanC_fermiW, norm_zero, show (1 : ℝ) + 0 ^ 2 = 1 by norm_num, Real.sqrt_one,
        one_smul]) (by rw [nib_nrmC_fermiW, h])
  · rintro ⟨v, rfl⟩
    exact nrmC_phi m v

lemma nearIdAt_blk_axis (m : ℕ) (hA1 : POActionProp 1) (hI1 : HypIsometryProp 1)
    (hA : POActionProp (1 + m)) (hI : HypIsometryProp (1 + m))
    {R : E m ≃ₗᵢ[ℝ] E m} {c θ : ℝ} (hc : 0 ≤ c) (hrot : rotN R ≤ c) (hθ : 6 * c < θ)
    (x : E (1 + m)) (hx : nrmC 1 m x = 0) :
    NearIdAt (blk 1 m 1 R) x θ := by
  intro u hu
  set W := nrmC 1 m u with hW
  set v := (Real.sqrt (1 + ‖W‖ ^ 2))⁻¹ • tanC 1 m u with hv
  have hu' : fermiW 1 m v W = u := by rw [hv, hW]; exact nib_fermiW_surj m u
  have hx' : fermiW 1 m (tanC 1 m x) 0 = x := by
    refine nib_eq_of_tanC_nrmC ?_ ?_
    · rw [nib_tanC_fermiW, norm_zero,
        show (1 : ℝ) + 0 ^ 2 = 1 by norm_num, Real.sqrt_one, one_smul]
    · rw [nib_nrmC_fermiW, hx]
  have hh : hdist (fermiW 1 m (tanC 1 m x) 0) (fermiW 1 m v W) ≤ 1 := by
    rw [hx', hu']; exact hu
  have hb := nib_disp_bound m R (tanC 1 m x) v 0 W c hc hrot (by simpa using hc) hh
  have key : hdist u (blk 1 m 1 R • u) ≤ ‖R W - W‖ := by
    rw [← hu']
    exact nib_hdist_blk_le_disp m hA1 hI1 hA hI R v W
  exact lt_of_le_of_lt key (lt_of_le_of_lt hb hθ)

/-! ## Monotonicity and conjugation of `NearIdAt` -/

lemma NearIdAt.mono {n : ℕ} {g : PO n 1} {z : E n} {η η' : ℝ} (h : NearIdAt g z η)
    (hle : η ≤ η') : NearIdAt g z η' := fun u hu => lt_of_lt_of_le (h u hu) hle

lemma nearIdAt_conj_iff {n : ℕ} (hA : POActionProp n) (hI : HypIsometryProp n)
    (g b : PO n 1) (p : E n) (θ : ℝ) :
    NearIdAt (g⁻¹ * b * g) p θ ↔ NearIdAt b (g • p) θ := by
  have hb := POBasic.ofProp hA
  have hid := HypIsoData.ofProp hI
  have hconj : ∀ u : E n, (g⁻¹ * b * g) • u = g⁻¹ • (b • (g • u)) := by
    intro u
    rw [hb.mul_smul (g⁻¹ * b) g u, hb.mul_smul g⁻¹ b (g • u)]
  have hginv : ∀ u : E n, g⁻¹ • (g • u) = u := by
    intro u; rw [← hb.mul_smul g⁻¹ g u, inv_mul_cancel, hb.one_smul]
  have hgapp : ∀ u : E n, g • (g⁻¹ • u) = u := by
    intro u; rw [← hb.mul_smul g g⁻¹ u, mul_inv_cancel, hb.one_smul]
  constructor
  · intro h u hu
    have hu' : hdist p (g⁻¹ • u) ≤ 1 := by
      have : hdist p (g⁻¹ • u) = hdist (g • p) (g • (g⁻¹ • u)) :=
        (hid.isom_smul g p (g⁻¹ • u)).symm
      rw [this, hgapp u]
      exact hu
    have h2 := h (g⁻¹ • u) hu'
    have h3 : (g⁻¹ * b * g) • (g⁻¹ • u) = g⁻¹ • (b • u) := by
      rw [hconj (g⁻¹ • u), hgapp u]
    rw [h3] at h2
    have h4 : hdist u (b • u) = hdist (g⁻¹ • u) (g⁻¹ • (b • u)) :=
      (hid.isom_smul g⁻¹ u (b • u)).symm
    rwa [h4]
  · intro h u hu
    have hu' : hdist (g • p) (g • u) ≤ 1 := by
      rw [hid.isom_smul g p u]
      exact hu
    have h2 := h (g • u) hu'
    have h3 : (g⁻¹ * b * g) • u = g⁻¹ • (b • (g • u)) := hconj u
    rw [h3]
    have h4 : hdist u (g⁻¹ • (b • (g • u))) = hdist (g • u) (b • (g • u)) := by
      rw [← hid.isom_smul g u (g⁻¹ • (b • (g • u))), hgapp (b • (g • u))]
    rw [h4]
    exact h2

/-! ## Isometries of `ℝ` -/

lemma abs_isometry_classify {f : ℝ → ℝ} (hf0 : f 0 = 0)
    (hf : ∀ x y : ℝ, |f x - f y| = |x - y|) :
    (∀ x, f x = x) ∨ (∀ x, f x = -x) := by
  have hsign : ∀ x : ℝ, f x = x ∨ f x = -x := by
    intro x
    have h : |f x| = |x| := by simpa [hf0] using hf x 0
    exact abs_eq_abs.mp h
  have hkey : ∀ x y : ℝ, f x = x → f y = -y → x * y = 0 := by
    intro x y hfx hfy
    have h := hf x y
    rw [hfx, hfy, sub_neg_eq_add] at h
    rcases abs_eq_abs.mp h with h2 | h2
    · have : y = 0 := by linarith
      rw [this, mul_zero]
    · have : x = 0 := by linarith
      rw [this, zero_mul]
  by_cases h1 : f 1 = 1
  · left
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · exact hf0
    · rcases hsign x with hx1 | hx1
      · exact hx1
      · exact absurd (hkey 1 x h1 hx1) (by simpa using hx)
  · right
    intro x
    have h1' : f 1 = -1 := by
      rcases hsign 1 with h | h
      · exact absurd h h1
      · exact h
    rcases eq_or_ne x 0 with rfl | hx
    · rw [hf0]; norm_num
    · rcases hsign x with hx1 | hx1
      · exact absurd (hkey x 1 hx1 h1') (by simpa using hx)
      · exact hx1

lemma real_isometry_classify {ρ : ℝ → ℝ} (hρ : ∀ s t : ℝ, |ρ s - ρ t| = |s - t|) {tp : ℝ}
    (htp : ρ tp = tp) : (∀ t, ρ t = t) ∨ (∀ t, ρ t = 2 * tp - t) := by
  set f : ℝ → ℝ := fun t => ρ (t + tp) - tp with hf
  have hf0 : f 0 = 0 := by simp [hf, htp]
  have hfiso : ∀ x y : ℝ, |f x - f y| = |x - y| := by
    intro x y
    have h : f x - f y = ρ (x + tp) - ρ (y + tp) := by simp only [hf]; ring
    rw [h, hρ]
    congr 1
    ring
  rcases abs_isometry_classify hf0 hfiso with h | h
  · left
    intro t
    have := h (t - tp)
    simp only [hf] at this
    rw [sub_add_cancel] at this
    linarith
  · right
    intro t
    have := h (t - tp)
    simp only [hf] at this
    rw [sub_add_cancel] at this
    linarith

/-! ## The final geometric step -/

lemma flips_fix_geodesic {m : ℕ} (hA : POActionProp (1 + m)) (hI : HypIsometryProp (1 + m))
    (a : PO (1 + m) 1) (ψ : ℝ → E (1 + m)) (tp θ : ℝ)
    (hψ : ∀ s t, hdist (ψ s) (ψ t) = |s - t|)
    (hpre : ∀ t, ∃ t', a • (ψ t) = ψ t')
    (hfix : a • (ψ tp) = ψ tp)
    (hnear : NearIdAt a (ψ tp) θ) (hθ : θ < 2) :
    ∀ t, a • (ψ t) = ψ t := by
  have hid := HypIsoData.ofProp hI
  choose ρ hρ using hpre
  have hinj : Function.Injective ψ := by
    intro s t hst
    have h := hψ s t
    rw [hst] at h
    have h2 : |s - t| = 0 := by rw [← h, hψ t t]; simp
    exact sub_eq_zero.mp (abs_eq_zero.mp h2)
  have hiso : ∀ s t : ℝ, |ρ s - ρ t| = |s - t| := by
    intro s t
    have h1 : hdist (ψ (ρ s)) (ψ (ρ t)) = hdist (ψ s) (ψ t) := by
      simpa only [← hρ s, ← hρ t] using hid.isom_smul a (ψ s) (ψ t)
    simpa only [hψ] using h1
  have hρtp : ρ tp = tp := hinj (by rw [← hρ tp, hfix])
  rcases real_isometry_classify hiso hρtp with h | h
  · intro t; rw [hρ t, h t]
  · exfalso
    have h1 : hdist (ψ (tp + 1)) (a • ψ (tp + 1)) = 2 := by
      rw [hρ (tp + 1), h (tp + 1), hψ]
      rw [show tp + 1 - (2 * tp - (tp + 1)) = 2 by ring]
      norm_num
    have h2 : hdist (ψ tp) (ψ (tp + 1)) ≤ 1 := by
      rw [hψ, show tp - (tp + 1) = -1 by ring]
      norm_num
    have h3 := hnear (ψ (tp + 1)) h2
    linarith

/-! ## The main theorem -/

theorem conjCountGeodV2 (m : ℕ) (hm : 1 ≤ m)
    (hA1 : Submission.Mostow.POActionProp 1) (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m)) :
    ∃ η_Z : ℝ, 0 < η_Z ∧ η_Z < 2 ∧
      ∀ (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)),
        IsDiscrete (SetLike.coe Λ) →
      ∀ (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
        (b : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1), b ∈ Λ →
        b = Submission.Mostow.blk 1 m 1 R →
        (∀ W : Submission.Mostow.E m, R W = W → W = 0) →
        ∀ (w : Submission.Mostow.E (1 + m)),
          ∀ (g : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1), g ∈ Λ →
          Submission.Mostow.NearIdAt b w η_Z →
          Submission.Mostow.NearIdAt (g⁻¹ * b * g) w η_Z →
          g ∈ Submission.Mostow.SetStabStd 1 m := by
  have hm2 : 2 ≤ 1 + m := by omega
  obtain ⟨θZ, hθZpos, hθZ⟩ := Work.Mostow.gapA.nilpotentPairNearIdAt (1 + m) hm2 hA hI
  obtain ⟨θF, hθFpos, hθF⟩ := Work.Mostow.frobeniusCommute (1 + m) hm2 hA hI
  refine ⟨min (1 / 100) (min (θZ / 2) (θF / 100)),
    lt_min (by norm_num) (lt_min (by linarith [hθZpos]) (by linarith [hθFpos])), ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  · intro Λ hdisc R b hbΛ hbR hRnz w g hg h1 h2
    have hb := POBasic.ofProp hA
    have hid := HypIsoData.ofProp hI
    set η : ℝ := min (1 / 100) (min (θZ / 2) (θF / 100)) with hηdef
    have hη_le_100 : η ≤ 1 / 100 := le_trans (le_of_eq hηdef) (min_le_left _ _)
    have hη_le_2 : η ≤ min (θZ / 2) (θF / 100) :=
      le_trans (le_of_eq hηdef) (min_le_right _ _)
    have hη_le_Z : η ≤ θZ / 2 := le_trans hη_le_2 (min_le_left _ _)
    have hη_le_F : η ≤ θF / 100 := le_trans hη_le_2 (min_le_right _ _)
    have hη_lt_Z : η < θZ := lt_of_le_of_lt hη_le_Z (by linarith)
    have hη24F : 24 * η < θF := by nlinarith [hη_le_F, hθFpos]
    have hη241 : 24 * η < 1 := by linarith [hη_le_100]
    have hη_le_1 : η ≤ 1 := by linarith [hη_le_100]
    have hηpos : 0 < η := by
      rw [hηdef]
      exact lt_min (by norm_num) (lt_min (by linarith [hθZpos]) (by linarith [hθFpos]))
    -- the conjugated element
    set c : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1 := g⁻¹ * b * g with hcdef
    have hcz : NearIdAt c w η := h2
    have hcmem : c ∈ Λ := by
      rw [hcdef]; exact Λ.mul_mem (Λ.mul_mem (Λ.inv_mem hg) hbΛ) hg
    have hb1 : NearIdAt (blk 1 m 1 R) w η := by rw [← hbR]; exact h1
    -- torsion
    have hfixpt : b • (fermiW 1 m 0 0) = fermiW 1 m 0 0 := by
      rw [hbR, nib_blk_smul_fermiW m hA1 hI1 hA hI R 0 0]
      simp
    have hp₁ : c • (g⁻¹ • (fermiW 1 m 0 0)) = g⁻¹ • (fermiW 1 m 0 0) := by
      rw [hcdef, hb.mul_smul (g⁻¹ * b) g, hb.mul_smul g⁻¹ b]
      have h2' : g • (g⁻¹ • (fermiW 1 m 0 0)) = fermiW 1 m 0 0 := by
        rw [← hb.mul_smul g g⁻¹, mul_inv_cancel, hb.one_smul]
      rw [h2', hfixpt]
    have htorb : IsOfFinOrder b :=
      (Submonoid.isOfFinOrder_coe).mpr
        (isOfFinOrder_of_fixed hA hI Λ hdisc ⟨b, hbΛ⟩ (fermiW 1 m 0 0) hfixpt)
    have htorc : IsOfFinOrder c :=
      (Submonoid.isOfFinOrder_coe).mpr
        (isOfFinOrder_of_fixed hA hI Λ hdisc ⟨c, hcmem⟩ (g⁻¹ • (fermiW 1 m 0 0)) hp₁)
    -- Zassenhaus at `w`
    have hnbZ : NearIdAt b w θZ := NearIdAt.mono h1 (le_of_lt hη_lt_Z)
    have hncZ : NearIdAt c w θZ := NearIdAt.mono hcz (le_of_lt hη_lt_Z)
    have hnil : Group.IsNilpotent (Subgroup.closure ({b, c} : Set (PO (1 + m) 1))) :=
      hθZ Λ hdisc w ⟨b, hbΛ⟩ ⟨c, hcmem⟩ hnbZ hncZ
    set H : Subgroup (PO (1 + m) 1) := Subgroup.closure ({b, c} : Set (PO (1 + m) 1))
      with hHdef
    have hbH : b ∈ H := by rw [hHdef]; exact Subgroup.subset_closure (by simp)
    have hcH : c ∈ H := by rw [hHdef]; exact Subgroup.subset_closure (by simp)
    haveI hHnil : Group.IsNilpotent ↥H := hnil
    haveI hHfg : Group.FG ↥H := Group.closure_finite_fg ({b, c} : Set (PO (1 + m) 1))
    have hgen : Subgroup.closure {h : ↥H | IsOfFinOrder h} = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro x
      have hbHt : IsOfFinOrder (⟨b, hbH⟩ : ↥H) := (Submonoid.isOfFinOrder_coe).mp htorb
      have hcHt : IsOfFinOrder (⟨c, hcH⟩ : ↥H) := (Submonoid.isOfFinOrder_coe).mp htorc
      have hsub : H ≤ (Subgroup.closure {h : ↥H | IsOfFinOrder h}).map H.subtype := by
        rw [hHdef, Subgroup.closure_le]
        intro y hy
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact ⟨_, Subgroup.subset_closure hbHt, rfl⟩
        · exact ⟨_, Subgroup.subset_closure hcHt, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hsub x.2
      have hyx' : y = x := Subtype.ext hyx
      rwa [hyx'] at hy
    haveI hHfin : Finite ↥H := nilp_torsionGen_finite hgen
    obtain ⟨p, hp⟩ := fixPoint_of_finite hA H hHfin
    have hbp : b • p = p := hp b hbH
    have hcp : c • p = p := hp c hcH
    -- `rotN` bound on `R` from the near-identity of `b` at `w`
    set Ww := nrmC 1 m w with hWw
    set vw := (Real.sqrt (1 + ‖Ww‖ ^ 2))⁻¹ • tanC 1 m w with hvw
    have hwv : fermiW 1 m vw Ww = w := by rw [hvw, hWw]; exact nib_fermiW_surj m w
    have hb1' : NearIdAt (blk 1 m 1 R) (fermiW 1 m vw Ww) η := by rw [hwv]; exact hb1
    obtain ⟨hrotR, hdispR⟩ := (nearId_blk m hA1 hI1 hA hI R vw Ww).2 η hb1' hη_le_1
    -- points of the axis are near-identity points for `b`
    have hnear_b : ∀ (x : E (1 + m)), nrmC 1 m x = 0 → ∀ θ : ℝ, 24 * η < θ → NearIdAt b x θ := by
      intro x hx θ hθ
      rw [hbR]
      exact nearIdAt_blk_axis m hA1 hI1 hA hI (by linarith) hrotR (by linarith) x hx
    -- fixed points of `b` are exactly the standard stratum
    have hfixb : ∀ y : E (1 + m), b • y = y ↔ y ∈ Set.range (phi m) := by
      intro y
      rw [hbR]
      exact (blk_fixed_iff m hA1 hI1 hA hI R hRnz y).trans (nrmC_eq_zero_iff m y)
    have hp_range : p ∈ Set.range (phi m) := (hfixb p).mp hbp
    have hp_nrm : nrmC 1 m p = 0 := (nrmC_eq_zero_iff m p).mpr hp_range
    have hnear_b_p : ∀ θ : ℝ, 24 * η < θ → NearIdAt b p θ := hnear_b p hp_nrm
    -- `g p` is also on the axis
    have hgapp : ∀ u : E (1 + m), g • (g⁻¹ • u) = u := fun u => by
      rw [← hb.mul_smul g g⁻¹ u, mul_inv_cancel, hb.one_smul]
    have hginv : ∀ u : E (1 + m), g⁻¹ • (g • u) = u := fun u => by
      rw [← hb.mul_smul g⁻¹ g u, inv_mul_cancel, hb.one_smul]
    have hpgp : b • (g • p) = g • p := by
      have h1' : g • (c • p) = g • p := by rw [hcp]
      have h2' : g • (c • p) = b • (g • p) := by
        rw [hcdef, hb.mul_smul (g⁻¹ * b) g, hb.mul_smul g⁻¹ b]
        rw [hgapp (b • (g • p))]
      rw [← h2']; exact h1'
    have hgp_range : g • p ∈ Set.range (phi m) := (hfixb (g • p)).mp hpgp
    have hgp_nrm : nrmC 1 m (g • p) = 0 := (nrmC_eq_zero_iff m (g • p)).mpr hgp_range
    have hnear_c_p : ∀ θ : ℝ, 24 * η < θ → NearIdAt c p θ := by
      intro θ hθ
      rw [hcdef, nearIdAt_conj_iff hA hI g b p θ]
      exact hnear_b (g • p) hgp_nrm θ hθ
    have hnear_b_F : NearIdAt b p θF := hnear_b_p θF hη24F
    have hnear_c_F : NearIdAt c p θF := hnear_c_p θF hη24F
    -- commutativity (Frobenius)
    have hcomm : b * c = c * b := hθF H hHfin p hp b hbH c hcH hnear_b_F hnear_c_F
    have hcomm_bc : ∀ x : E (1 + m), b • (c • x) = c • (b • x) := by
      intro x
      rw [← hb.mul_smul b c x, hcomm, hb.mul_smul c b x]
    have hcomm_cb : ∀ x : E (1 + m), c • (b • x) = b • (c • x) :=
      fun x => (hcomm_bc x).symm
    have hθ0lt : min θF 1 < 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hmin24 : 24 * η < min θF 1 := lt_min hη24F hη241
    have hnear_b_p0 : NearIdAt b p (min θF 1) := hnear_b_p _ hmin24
    have hnear_c_p0 : NearIdAt c p (min θF 1) := hnear_c_p _ hmin24
    -- first flip argument: `c` fixes the axis of `b` pointwise
    have hpre1 : ∀ t : ℝ, ∃ t', c • (arcGeo m t) = arcGeo m t' := by
      intro t
      have hfixpsi : b • (arcGeo m t) = arcGeo m t :=
        (hfixb (arcGeo m t)).mpr (Set.mem_range.mpr ⟨e1 (Real.sinh t), rfl⟩)
      have hc : b • (c • (arcGeo m t)) = c • (arcGeo m t) := by
        rw [hcomm_bc, hfixpsi]
      have hmem : c • (arcGeo m t) ∈ Set.range (phi m) := (hfixb _).mp hc
      obtain ⟨v, hv⟩ := hmem
      exact ⟨Real.arsinh (v 0), by rw [← hv, arcGeo_arsinh]⟩
    have hp_arc : ∃ t : ℝ, arcGeo m t = p := by
      obtain ⟨v, hv⟩ := hp_range
      exact ⟨Real.arsinh (v 0), by rw [arcGeo_arsinh]; exact hv⟩
    obtain ⟨tp1, htp1⟩ := hp_arc
    have hfix1 : c • (arcGeo m tp1) = arcGeo m tp1 := by rw [htp1]; exact hcp
    have hnear1 : NearIdAt c (arcGeo m tp1) (min θF 1) := by rw [htp1]; exact hnear_c_p0
    have hcFixes : ∀ t : ℝ, c • (arcGeo m t) = arcGeo m t :=
      flips_fix_geodesic hA hI c (arcGeo m) tp1 (min θF 1)
        (hdist_arcGeo m) hpre1 hfix1 hnear1 hθ0lt
    -- second flip argument: `b` fixes the fixed set of `c` pointwise
    set arcGeo2 : ℝ → E (1 + m) := fun t => g⁻¹ • arcGeo m t with harc2
    have hFixc : ∀ y : E (1 + m), c • y = y ↔ g • y ∈ Set.range (phi m) := by
      intro y
      have h1' : c • y = g⁻¹ • (b • (g • y)) := by
        rw [hcdef, hb.mul_smul (g⁻¹ * b) g, hb.mul_smul g⁻¹ b]
      rw [h1']
      constructor
      · intro h
        have h2' : g • (g⁻¹ • (b • (g • y))) = g • y := by rw [h]
        rw [hgapp (b • (g • y))] at h2'
        exact (hfixb (g • y)).mp h2'
      · intro h
        rw [(hfixb (g • y)).mpr h, hginv y]
    have hFixc_range : ∀ y : E (1 + m), c • y = y ↔ y ∈ Set.range arcGeo2 := by
      intro y
      rw [hFixc y]
      constructor
      · rintro ⟨v, hv⟩
        refine ⟨Real.arsinh (v 0), ?_⟩
        simp only [harc2]
        rw [arcGeo_arsinh, hv, hginv]
      · rintro ⟨t, rfl⟩
        simp only [harc2]
        rw [hgapp]
        exact ⟨e1 (Real.sinh t), rfl⟩
    have hψ2 : ∀ s t : ℝ, hdist (arcGeo2 s) (arcGeo2 t) = |s - t| := by
      intro s t
      simp only [harc2]
      rw [hid.isom_smul, hdist_arcGeo]
    have hpre2 : ∀ t : ℝ, ∃ t', b • (arcGeo2 t) = arcGeo2 t' := by
      intro t
      have hfixpsi : b • (arcGeo m t) = arcGeo m t :=
        (hfixb (arcGeo m t)).mpr (Set.mem_range.mpr ⟨e1 (Real.sinh t), rfl⟩)
      have hc2 : c • (arcGeo2 t) = arcGeo2 t := by
        simp only [harc2]
        rw [show c • (g⁻¹ • arcGeo m t) = g⁻¹ • (b • (g • (g⁻¹ • arcGeo m t))) by
              rw [hcdef, hb.mul_smul (g⁻¹ * b) g, hb.mul_smul g⁻¹ b]]
        rw [hgapp (arcGeo m t), hfixpsi]
      have hc3 : c • (b • (arcGeo2 t)) = b • (arcGeo2 t) := by
        rw [hcomm_cb, hc2]
      obtain ⟨v, hv⟩ := (hFixc (b • (arcGeo2 t))).mp hc3
      have hv' : phi m v = g • (b • (g⁻¹ • arcGeo m t)) := by simpa [harc2] using hv
      refine ⟨Real.arsinh (v 0), ?_⟩
      simp only [harc2]
      rw [arcGeo_arsinh, hv', hginv]
    have hp_arc2 : ∃ t : ℝ, arcGeo2 t = p := by
      obtain ⟨v, hv⟩ := (hFixc p).mp hcp
      refine ⟨Real.arsinh (v 0), ?_⟩
      simp only [harc2]
      rw [arcGeo_arsinh, hv, hginv]
    obtain ⟨tp2, htp2⟩ := hp_arc2
    have hfix2 : b • (arcGeo2 tp2) = arcGeo2 tp2 := by rw [htp2]; exact hbp
    have hnear2 : NearIdAt b (arcGeo2 tp2) (min θF 1) := by rw [htp2]; exact hnear_b_p0
    have hbFixes : ∀ t : ℝ, b • (arcGeo2 t) = arcGeo2 t :=
      flips_fix_geodesic hA hI b arcGeo2 tp2 (min θF 1)
        hψ2 hpre2 hfix2 hnear2 hθ0lt
    -- conclusion
    have hcfix2 : ∀ y : E (1 + m), y ∈ Set.range (phi m) → c • y = y := by
      intro y hy
      have hmem : y ∈ Set.range (arcGeo m) := by rw [range_arcGeo m]; exact hy
      obtain ⟨t, ht⟩ := hmem
      rw [← ht]; exact hcFixes t
    have hb_on_Fixc : ∀ y : E (1 + m), c • y = y → b • y = y := by
      intro y hy
      rw [hFixc_range] at hy
      obtain ⟨t, ht⟩ := hy
      rw [← ht]; exact hbFixes t
    show ∀ u : E (1 + m), u ∈ stdTG 1 m ↔ g • u ∈ stdTG 1 m
    intro u
    rw [← range_phi m]
    constructor
    · intro hu
      rw [← hFixc u]
      exact hcfix2 u hu
    · intro hu
      have hcu : c • u = u := (hFixc u).mpr hu
      rw [← hfixb u]
      exact hb_on_Fixc u hcu

end
end Work.Mostow
