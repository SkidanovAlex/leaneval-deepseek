import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Submission.Commons.Measure.Integration.nonneg_integral_eq_lam
import Submission.Commons.Measure.Integration.integrable_nonneg_of_contDiff_tsupport_subset
import Submission.Commons.Analysis.Calculus.BumpFunction.contDiff_eq_one_on_isCompact_tsupport_subset
import Submission.Commons.Analysis.Calculus.BumpFunction.contDiff_eq_one_on_isClosed_tsupport_subset

namespace Commons.Measure.Distribution

open MeasureTheory Metric Set Filter Function
open scoped ContDiff ENNReal Topology NNReal CompactlySupported RealInnerProductSpace InnerProductSpace
open Commons.Analysis.Calculus.BumpFunction

noncomputable section

variable {W : Type*} [TopologicalSpace W] [T2Space W] {u : Set W}

/-- Extension by zero to `W` of a compactly supported continuous function on the subset `u`. -/
def zext (f : C_c(u, ℝ)) : W → ℝ := Function.extend Subtype.val f 0

lemma zext_apply_of_mem (f : C_c(u, ℝ)) {x : W} (hx : x ∈ u) : zext f x = f ⟨x, hx⟩ := by
  rw [zext]; exact Subtype.val_injective.extend_apply f 0 ⟨x, hx⟩

lemma zext_apply_of_notMem (f : C_c(u, ℝ)) {x : W} (hx : x ∉ u) : zext f x = 0 := by
  rw [zext]
  exact extend_apply' _ _ x (by rintro ⟨y, hy⟩; exact hx (hy ▸ y.2))

lemma zext_zero : zext (0 : C_c(u, ℝ)) = 0 := by
  funext x
  by_cases hx : x ∈ u
  · rw [zext_apply_of_mem _ hx]; rfl
  · rw [zext_apply_of_notMem _ hx]; rfl

lemma zext_add (f g : C_c(u, ℝ)) : zext (f + g) = zext f + zext g := by
  funext x
  by_cases hx : x ∈ u
  · rw [zext_apply_of_mem _ hx, Pi.add_apply, zext_apply_of_mem _ hx, zext_apply_of_mem _ hx]; rfl
  · rw [zext_apply_of_notMem _ hx, Pi.add_apply, zext_apply_of_notMem _ hx,
      zext_apply_of_notMem _ hx, add_zero]

lemma zext_smul (a : ℝ) (f : C_c(u, ℝ)) : zext (a • f) = a • zext f := by
  funext x
  by_cases hx : x ∈ u
  · rw [zext_apply_of_mem _ hx, Pi.smul_apply, zext_apply_of_mem _ hx]; rfl
  · rw [zext_apply_of_notMem _ hx, Pi.smul_apply, zext_apply_of_notMem _ hx, smul_zero]

lemma tsupport_zext_subset (f : C_c(u, ℝ)) : tsupport (zext f) ⊆ u := by
  have h := HasCompactSupport.tsupport_extend_zero (f := (f : u → ℝ)) (g := Subtype.val)
      f.hasCompactSupport' continuous_subtype_val Subtype.val_injective
  rw [zext, h]
  rintro x ⟨y, -, rfl⟩
  exact y.2

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {t : Set Y}

/-- Pack a compactly supported continuous function on `Y` supported in `t` as an element of
`C_c(t, ℝ)`. -/
def toCc (f : Y → ℝ) (hf : Continuous f) (hcomp : HasCompactSupport f) (hsub : tsupport f ⊆ t) :
    C_c(t, ℝ) where
  toFun z := f z
  continuous_toFun := hf.comp continuous_subtype_val
  hasCompactSupport' := by
    rw [hasCompactSupport_def]
    have hle : tsupport (fun z : t => f z) ⊆ Subtype.val ⁻¹' tsupport f :=
      closure_minimal (fun z hz => subset_tsupport f hz)
        ((isClosed_tsupport f).preimage continuous_subtype_val)
    exact (Topology.IsInducing.subtypeVal.isCompact_preimage' hcomp.isCompact
      (by simpa [Subtype.range_coe] using hsub)).of_isClosed_subset
      (isClosed_tsupport (fun z : t => f z)) hle

lemma zext_toCc (f : Y → ℝ) (hf : Continuous f) (hcomp : HasCompactSupport f)
    (hsub : tsupport f ⊆ t) : zext (toCc f hf hcomp hsub) = f := by
  funext x
  by_cases hx : x ∈ t
  · rw [zext_apply_of_mem _ hx]; rfl
  · rw [zext_apply_of_notMem _ hx]
    exact (image_eq_zero_of_notMem_tsupport (fun hx' => hx (hsub hx'))).symm

section PosSMulInner
variable {Z : Type*} [TopologicalSpace Z] {v : Set Z}
instance instPosSMulMono : PosSMulMono ℝ C_c(v, ℝ) where
  smul_le_smul_of_nonneg_left a ha b c hbc := by
    intro z
    exact mul_le_mul_of_nonneg_left (hbc z) ha
end PosSMulInner

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {r : Set V}

/-- The submodule of compactly supported continuous functions on `r` whose extension by zero
to `V` is smooth. -/
def smoothSub (r : Set V) : Submodule ℝ C_c(r, ℝ) where
  carrier := {f | ContDiff ℝ ∞ (zext f)}
  zero_mem' := by
    change ContDiff ℝ ∞ (zext (0 : C_c(r, ℝ)))
    rw [zext_zero]; exact contDiff_const
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_ofPred_eq] at hf hg
    change ContDiff ℝ ∞ (zext (f + g))
    rw [zext_add]
    exact hf.add hg
  smul_mem' := by
    intro a f hf
    simp only [Set.mem_ofPred_eq] at hf
    change ContDiff ℝ ∞ (zext (a • f))
    rw [zext_smul]
    exact hf.const_smul a

variable {Λ : (V → ℝ) → ℝ}
  (hadd0 : ∀ φ ψ, ContDiff ℝ ∞ φ → tsupport φ ⊆ r →
    ContDiff ℝ ∞ ψ → tsupport ψ ⊆ r → Λ (φ + ψ) = Λ φ + Λ ψ)
  (hsmul0 : ∀ (a : ℝ) φ, ContDiff ℝ ∞ φ → tsupport φ ⊆ r → Λ (a • φ) = a * Λ φ)

/-- The linear functional induced by `Λ` on the smooth compactly supported functions on `r`. -/
def smoothLinear : smoothSub r →ₗ[ℝ] ℝ where
  toFun f := Λ (zext (f : C_c(r, ℝ)))
  map_add' f g := by
    change Λ (zext ((f : C_c(r, ℝ)) + (g : C_c(r, ℝ)))) = Λ (zext (f : C_c(r, ℝ))) + Λ (zext (g : C_c(r, ℝ)))
    rw [zext_add]
    exact hadd0 _ _ f.2 (tsupport_zext_subset _) g.2 (tsupport_zext_subset _)
  map_smul' a f := by
    change Λ (zext (a • (f : C_c(r, ℝ)))) = a * Λ (zext (f : C_c(r, ℝ)))
    rw [zext_smul]
    exact hsmul0 a _ f.2 (tsupport_zext_subset _)

/-- `Λ` as a partially defined linear functional on `C_c(r, ℝ)`. -/
def partialLM : C_c(r, ℝ) →ₗ.[ℝ] ℝ := ⟨smoothSub r, smoothLinear hadd0 hsmul0⟩

section Bump

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]

/-- A smooth radial cutoff, equal to `1` on the ball of radius `n+1` and `0` outside the ball of
radius `√2 (n+1)`, increasing in `n`. -/
def eta (n : ℕ) : X → ℝ :=
  fun x : X => Real.smoothTransition (2 - ((n : ℝ) + 1)⁻¹ ^ 2 * inner ℝ x x)

lemma eta_contDiff (n : ℕ) : ContDiff ℝ ∞ (eta (X := X) n) := by
  unfold eta
  refine Real.smoothTransition.contDiff.comp ?_
  have h1 : ContDiff ℝ ∞ (fun x : X => inner ℝ x x) :=
    (contDiff_inner (E := X)).comp (contDiff_id.prodMk contDiff_id)
  have h2 : ContDiff ℝ ∞ (fun x : X => ((n:ℝ)+1)⁻¹^2 * inner ℝ x x) :=
    (contDiff_const (c := ((n:ℝ)+1)⁻¹^2)).mul h1
  exact (contDiff_const (c := (2:ℝ))).sub h2

lemma eta_nonneg (n : ℕ) (x : X) : 0 ≤ eta n x := Real.smoothTransition.nonneg _

lemma eta_le_one (n : ℕ) (x : X) : eta n x ≤ 1 := Real.smoothTransition.le_one _

lemma eta_eq_one (n : ℕ) {x : X} (hx : ‖x‖ ≤ (n : ℝ) + 1) : eta n x = 1 := by
  rw [eta, real_inner_self_eq_norm_sq]
  apply Real.smoothTransition.one_of_one_le
  have hpos : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have h1 : ((n : ℝ) + 1)⁻¹ * ‖x‖ ≤ 1 := by
    rw [inv_mul_le_one₀ hpos]; exact hx
  have h2 : ((n : ℝ) + 1)⁻¹ ^ 2 * ‖x‖ ^ 2 = (((n : ℝ) + 1)⁻¹ * ‖x‖) ^ 2 := by ring
  have h3 : 0 ≤ ((n : ℝ) + 1)⁻¹ * ‖x‖ := by positivity
  nlinarith [h1, h2, h3, sq_nonneg (((n : ℝ) + 1)⁻¹ * ‖x‖), norm_nonneg x]

lemma eta_mono (x : X) : Monotone (fun n : ℕ => eta n x) := by
  intro m n hmn
  unfold eta
  apply Real.smoothTransition.monotone
  have hposm : (0:ℝ) < (m:ℝ) + 1 := by positivity
  have hposn : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have hmn' : (m:ℝ) + 1 ≤ (n:ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
  have hinv : ((n:ℝ)+1)⁻¹ ≤ ((m:ℝ)+1)⁻¹ := (inv_le_inv₀ hposn hposm).mpr hmn'
  have h4 : ((n:ℝ)+1)⁻¹^2 ≤ ((m:ℝ)+1)⁻¹^2 := by
    nlinarith [hinv, inv_nonneg.2 hposn.le]
  have hinner : 0 ≤ inner ℝ x x := real_inner_self_nonneg
  nlinarith [mul_le_mul_of_nonneg_right h4 hinner]

lemma eta_tendsto_one (x : X) : Tendsto (fun n : ℕ => eta n x) atTop (𝓝 1) := by
  have h0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ ^ 2 * inner ℝ x x) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      have h1a : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
        (@tendsto_natCast_atTop_atTop ℝ _ _ _ _).comp (Filter.tendsto_add_atTop_nat 1)
      have h1b : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp h1a
      simpa only [Nat.cast_add, Nat.cast_one] using h1b
    have h1' : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ ^ 2) atTop (𝓝 0) := by
      simpa using h1.pow 2
    simpa using h1'.mul tendsto_const_nhds
  have h2 : Tendsto (fun n : ℕ => 2 - ((n : ℝ) + 1)⁻¹ ^ 2 * inner ℝ x x) atTop (𝓝 2) := by
    simpa using tendsto_const_nhds.sub h0
  have h3 : Tendsto (fun n : ℕ => Real.smoothTransition (2 - ((n : ℝ) + 1)⁻¹ ^ 2 * inner ℝ x x))
      atTop (𝓝 1) := by
    have h4 := Real.smoothTransition.continuous.tendsto 2 |>.comp h2
    rwa [Function.comp_def, Real.smoothTransition.one_of_one_le (by norm_num : (1:ℝ) ≤ 2)] at h4
  simpa only [eta] using h3

lemma eta_tsupport_subset (n : ℕ) :
    tsupport (eta (X := X) n) ⊆ closedBall (0:X) (Real.sqrt 2 * ((n : ℝ) + 1)) := by
  refine closure_minimal ?_ (isCompact_closedBall (0:X) (Real.sqrt 2 * ((n : ℝ) + 1))).isClosed
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hcon
  rw [mem_closedBall, dist_zero_right, not_le] at hcon
  apply hx
  rw [eta, real_inner_self_eq_norm_sq]
  apply Real.smoothTransition.zero_of_nonpos
  have hpos : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have hprod : Real.sqrt 2 < ‖x‖ * ((n:ℝ)+1)⁻¹ := by
    have h1 := mul_lt_mul_of_pos_right hcon (show (0:ℝ) < ((n:ℝ)+1)⁻¹ by positivity)
    rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), mul_one] at h1
  have hkey : 2 < ((n : ℝ) + 1)⁻¹ ^ 2 * ‖x‖ ^ 2 := by
    have hsq2 : (Real.sqrt 2)^2 < (‖x‖ * ((n:ℝ)+1)⁻¹)^2 := by
      nlinarith [hprod, Real.sqrt_nonneg 2,
        mul_nonneg (norm_nonneg x) (inv_nonneg.mpr hpos.le)]
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at hsq2
    calc ((n:ℝ)+1)⁻¹ ^ 2 * ‖x‖^2 = (‖x‖ * ((n:ℝ)+1)⁻¹)^2 := by ring
      _ > 2 := hsq2
  linarith [hkey]

lemma eta_hasCompactSupport (n : ℕ) : HasCompactSupport (eta (X := X) n) := by
  rw [hasCompactSupport_def]
  exact IsCompact.of_isClosed_subset
    (isCompact_closedBall (0:X) (Real.sqrt 2 * ((n : ℝ) + 1)))
    (isClosed_tsupport (eta (X := X) n)) (eta_tsupport_subset n)

end Bump

section Phase1b

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  {s : Set X} {Λ : (X → ℝ) → ℝ}
  (hadd : ∀ φ ψ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → ContDiff ℝ ∞ ψ → tsupport ψ ⊆ s →
    Λ (φ + ψ) = Λ φ + Λ ψ)
  (hsmul : ∀ (a : ℝ) φ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → Λ (a • φ) = a * Λ φ)

lemma smoothSub_nonneg_mem (x : (partialLM hadd hsmul).domain)
    (hx : (x : C_c(s, ℝ)) ∈ PointedCone.positive ℝ C_c(s, ℝ)) :
    0 ≤ zext (x : C_c(s, ℝ)) := by
  have hx0 : 0 ≤ (x : C_c(s, ℝ)) := hx
  intro z
  by_cases hz : z ∈ s
  · rw [zext_apply_of_mem _ hz]; exact hx0 ⟨z, hz⟩
  · rw [zext_apply_of_notMem _ hz]; exact le_refl 0

lemma smoothSub_dense (hs : IsOpen s) (y : C_c(s, ℝ)) :
    ∃ x : (partialLM hadd hsmul).domain,
      (x : C_c(s, ℝ)) + y ∈ PointedCone.positive ℝ C_c(s, ℝ) := by
  obtain ⟨M, hM⟩ := y.hasCompactSupport'.exists_bound_of_continuous y.continuous
  set A : Set X := Subtype.val '' tsupport y with hAdef
  have hAc : IsCompact A := y.hasCompactSupport'.isCompact.image continuous_subtype_val
  have hAt : A ⊆ s := by rintro _ ⟨z, -, rfl⟩; exact z.2
  obtain ⟨G, hGcd, hGone, hGts, hGcomp, hGnn, hGle⟩ :=
    contDiff_eq_one_on_isCompact_tsupport_subset hAc hs hAt
  set g : C_c(s, ℝ) := toCc G hGcd.continuous hGcomp hGts with hgdef
  have hgmem : g ∈ smoothSub s := by
    change ContDiff ℝ ∞ (zext g)
    rw [hgdef, zext_toCc]
    exact hGcd
  refine ⟨⟨(max M 1) • g, (smoothSub s).smul_mem (max M 1) hgmem⟩, ?_⟩
  have hgz : ∀ z : s, (z : X) ∈ A → g z = 1 := by
    intro z hz
    rw [hgdef]
    change G (z : X) = 1
    exact hGone (z : X) hz
  have hgz0 : ∀ z : s, 0 ≤ g z := by
    intro z; rw [hgdef]; change 0 ≤ G (z : X); exact hGnn _
  intro z
  change 0 ≤ (((max M 1) • g + y) : C_c(s, ℝ)) z
  by_cases hz : z ∈ tsupport y
  · have h1 : g z = 1 := hgz z ⟨z, hz, rfl⟩
    have h2 : y z ≥ -(max M 1) := by
      have h3 : |y z| ≤ M := by simpa [Real.norm_eq_abs] using hM z
      have h4 : -M ≤ y z := (abs_le.mp h3).1
      linarith [le_max_left M 1]
    have hval : (((max M 1) • g + y) : C_c(s, ℝ)) z = max M 1 + y z := by
      rw [CompactlySupportedContinuousMap.add_apply,
        CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, h1, mul_one]
    rw [hval]; linarith
  · have hyz : y z = 0 := image_eq_zero_of_notMem_tsupport hz
    have hval : (((max M 1) • g + y) : C_c(s, ℝ)) z = (max M 1) * g z := by
      rw [CompactlySupportedContinuousMap.add_apply,
        CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, hyz, add_zero]
    rw [hval]; exact mul_nonneg (le_trans zero_le_one (le_max_right M 1)) (hgz0 z)

end Phase1b

theorem integral_eq_lam_general
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] {s : Set X} {Λ : (X → ℝ) → ℝ} {μ : Measure X}
    (hs : IsOpen s)
    (hint : ∀ f : X → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ s → Integrable f μ)
    (hadd : ∀ φ ψ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → ContDiff ℝ ∞ ψ → tsupport ψ ⊆ s →
      Λ (φ + ψ) = Λ φ + Λ ψ)
    (hsmul : ∀ (a : ℝ) φ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → Λ (a • φ) = a * Λ φ)
    (hpos : ∀ φ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → 0 ≤ φ → 0 ≤ Λ φ)
    (hCc : ∀ f : X → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ s →
      ∫ x, f x ∂μ = Λ f)
    {φ : X → ℝ} (hφ : ContDiff ℝ ∞ φ) (hsub : tsupport φ ⊆ s) :
    Integrable φ μ ∧ ∫ x, φ x ∂μ = Λ φ := by
  have tsupport_add : ∀ {A B : X → ℝ}, tsupport A ⊆ s → tsupport B ⊆ s → tsupport (A + B) ⊆ s := by
    intro A B hA hB
    have h1 : tsupport (A + B) ⊆ tsupport A ∪ tsupport B := by
      rw [tsupport]
      refine closure_minimal ?_ (IsClosed.union (isClosed_tsupport A) (isClosed_tsupport B))
      intro x hx
      rw [Function.mem_support] at hx
      have hx' : A x ≠ 0 ∨ B x ≠ 0 := by
        by_contra h; push_neg at h
        exact hx (by rw [Pi.add_apply, h.1, h.2, add_zero])
      rcases hx' with h | h
      · exact Or.inl (subset_tsupport A (Function.mem_support.mpr h))
      · exact Or.inr (subset_tsupport B (Function.mem_support.mpr h))
    exact h1.trans (Set.union_subset hA hB)
  have tsupport_sub : ∀ {A B : X → ℝ}, tsupport A ⊆ s → tsupport B ⊆ s → tsupport (A - B) ⊆ s := by
    intro A B hA hB
    have h1 : tsupport (A - B) ⊆ tsupport A ∪ tsupport B := by
      rw [tsupport]
      refine closure_minimal ?_ (IsClosed.union (isClosed_tsupport A) (isClosed_tsupport B))
      intro x hx
      rw [Function.mem_support] at hx
      have hx' : A x ≠ 0 ∨ B x ≠ 0 := by
        by_contra h; push_neg at h
        exact hx (by rw [Pi.sub_apply, h.1, h.2, sub_zero])
      rcases hx' with h | h
      · exact Or.inl (subset_tsupport A (Function.mem_support.mpr h))
      · exact Or.inr (subset_tsupport B (Function.mem_support.mpr h))
    exact h1.trans (Set.union_subset hA hB)
  have lam_sub : ∀ {A B : X → ℝ}, ContDiff ℝ ∞ A → tsupport A ⊆ s →
      ContDiff ℝ ∞ B → tsupport B ⊆ s → Λ (A - B) = Λ A - Λ B := by
    intro A B hA hAs hB hBs
    have h1 : ContDiff ℝ ∞ (A - B) := hA.sub hB
    have h2 : tsupport (A - B) ⊆ s := tsupport_sub hAs hBs
    have hAB : A = B + (A - B) := by
      funext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
    rw [hAB, hadd B (A - B) hB hBs h1 h2]; ring
  have hsq_ts : ∀ {f : X → ℝ}, tsupport f ⊆ s → tsupport (fun x => (f x)^2) ⊆ s := by
    intro f hf
    have h1 : Function.support (fun x => (f x)^2) ⊆ Function.support f :=
      Function.support_comp_subset (f := f) (g := fun y : ℝ => y^2) (by simp)
    exact (closure_mono h1).trans hf
  obtain ⟨θ, hθcd, hθone, hθts, hθnn, hθle⟩ :=
    contDiff_eq_one_on_isClosed_tsupport_subset (isClosed_tsupport φ) hs hsub
  have hbilin : ∫ x, φ x * θ x ∂μ = Λ (fun x => φ x * θ x) := by
    have hpcd : ContDiff ℝ ∞ (fun x => (φ x + θ x)^2) := (hφ.add hθcd).pow 2
    have hmcd : ContDiff ℝ ∞ (fun x => (φ x - θ x)^2) := (hφ.sub hθcd).pow 2
    have hp_ts : tsupport (fun x => (φ x + θ x)^2) ⊆ s := hsq_ts (tsupport_add hsub hθts)
    have hm_ts : tsupport (fun x => (φ x - θ x)^2) ⊆ s := hsq_ts (tsupport_sub hsub hθts)
    have h1 := Commons.Measure.Integration.nonneg_integral_eq_lam hint hadd hsmul hpos hCc hpcd hp_ts (fun x => sq_nonneg _)
    have h2 := Commons.Measure.Integration.nonneg_integral_eq_lam hint hadd hsmul hpos hCc hmcd hm_ts (fun x => sq_nonneg _)
    have hi1 := Commons.Measure.Integration.integrable_nonneg_of_contDiff_tsupport_subset hint hadd hsmul hpos hCc hpcd hp_ts
      (fun x => sq_nonneg _)
    have hi2 := Commons.Measure.Integration.integrable_nonneg_of_contDiff_tsupport_subset hint hadd hsmul hpos hCc hmcd hm_ts
      (fun x => sq_nonneg _)
    have hsub2 : ∫ x, ((φ x + θ x)^2 - (φ x - θ x)^2) ∂μ
        = Λ (fun x => (φ x + θ x)^2 - (φ x - θ x)^2) := by
      rw [integral_sub hi1 hi2, h1, h2]
      exact (lam_sub hpcd hp_ts hmcd hm_ts).symm
    have hfun : (fun x => (φ x + θ x)^2 - (φ x - θ x)^2) = fun x => 4 * (φ x * θ x) := by
      funext x; ring
    have hsm : Λ (fun x => 4 * (φ x * θ x)) = 4 * Λ (fun x => φ x * θ x) := by
      have h4 := hsmul 4 (fun x => φ x * θ x) (hφ.mul hθcd)
        (tsupport_mul_subset_left.trans hsub)
      have hfun4 : (fun x => 4 * (φ x * θ x)) = (4:ℝ) • (fun x => φ x * θ x) := by
        funext x; simp only [Pi.smul_apply]; ring
      rw [hfun4]
      exact h4
    rw [hfun] at hsub2
    rw [integral_const_mul, hsm] at hsub2
    linarith
  have hφθ : (fun x => φ x * θ x) = φ := by
    funext x
    by_cases hx : φ x = 0
    · simp [hx]
    · rw [hθone x (subset_tsupport φ (Function.mem_support.mpr hx)), mul_one]
  have hintφ : ∫ x, φ x ∂μ = Λ φ := by
    rw [hφθ] at hbilin
    exact hbilin
  have hsqφ : Integrable (fun x => (φ x)^2) μ :=
    Commons.Measure.Integration.integrable_nonneg_of_contDiff_tsupport_subset hint hadd hsmul hpos hCc (hφ.pow 2)
      (hsq_ts hsub) (fun x => sq_nonneg _)
  have hsqθ : Integrable (fun x => (θ x)^2) μ :=
    Commons.Measure.Integration.integrable_nonneg_of_contDiff_tsupport_subset hint hadd hsmul hpos hCc (hθcd.pow 2)
      (hsq_ts hθts) (fun x => sq_nonneg _)
  have hgint : Integrable (fun x => ((φ x)^2 + (θ x)^2)/2) μ := by
    simpa [Pi.add_apply, div_eq_mul_inv, mul_comm] using (hsqφ.add hsqθ).const_mul (1/2)
  have hle : ∀ᵐ x ∂μ, ‖φ x‖ ≤ ((φ x)^2 + (θ x)^2)/2 := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs]
    have h1 : |φ x| = |φ x| * θ x := by
      by_cases hx : φ x = 0
      · simp [hx]
      · rw [hθone x (subset_tsupport φ (Function.mem_support.mpr hx)), mul_one]
    rw [h1]
    nlinarith [sq_nonneg (|φ x| - θ x), hθnn x, abs_nonneg (φ x), sq_abs (φ x)]
  exact ⟨hgint.mono' hφ.continuous.aestronglyMeasurable hle, hintφ⟩


section Main

/-- Given a positive linear functional on the smooth compactly supported functions inside the open
set `s`, there is a measure supported in `s` representing it. -/
theorem exists_measure_of_positive_functional {n : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : IsOpen s)
    (Λ : (EuclideanSpace ℝ (Fin n) → ℝ) → ℝ)
    (hadd : ∀ φ ψ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → ContDiff ℝ ∞ ψ → tsupport ψ ⊆ s →
      Λ (φ + ψ) = Λ φ + Λ ψ)
    (hsmul : ∀ (a : ℝ) φ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → Λ (a • φ) = a * Λ φ)
    (hpos : ∀ φ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → 0 ≤ φ → 0 ≤ Λ φ) :
    ∃ μ : Measure (EuclideanSpace ℝ (Fin n)), μ sᶜ = 0 ∧
      ∀ φ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → ∫ x, φ x ∂μ = Λ φ := by
  classical
  obtain ⟨g, hgeq, hgpos⟩ := riesz_extension (PointedCone.positive ℝ C_c(s, ℝ))
    (partialLM hadd hsmul)
    (fun x hx => by
      change 0 ≤ Λ (zext (x : C_c(s, ℝ)))
      exact hpos _ x.2 (tsupport_zext_subset _) (smoothSub_nonneg_mem hadd hsmul x hx))
    (fun y => smoothSub_dense hadd hsmul hs y)
  haveI hlc : LocallyCompactSpace s := hs.locallyCompactSpace
  let Gpos : C_c(s, ℝ) →ₚ[ℝ] ℝ :=
    { toLinearMap := g
      monotone' := fun a b hab => by
        have h1 : 0 ≤ b - a := sub_nonneg.mpr hab
        have h2 : 0 ≤ g b - g a := by rw [← map_sub]; exact hgpos (b - a) h1
        exact sub_nonneg.mp h2 }
  set ν : Measure s := RealRMK.rieszMeasure Gpos with hνdef
  set μ : Measure (EuclideanSpace ℝ (Fin n)) := Measure.map Subtype.val ν with hμdef
  haveI : IsFiniteMeasureOnCompacts ν :=
    (RealRMK.regular_rieszMeasure Gpos).toIsFiniteMeasureOnCompacts
  refine ⟨μ, ?_, ?_⟩
  · have hmeas : Measurable (Subtype.val : s → EuclideanSpace ℝ (Fin n)) := measurable_subtype_coe
    have hpre : (Subtype.val : s → EuclideanSpace ℝ (Fin n)) ⁻¹' (sᶜ) = ∅ := by
      ext z; simp
    rw [hμdef, Measure.map_apply hmeas hs.isClosed_compl.measurableSet, hpre, measure_empty]
  · intro φ hφ hφs
    refine (integral_eq_lam_general hs ?_ hadd hsmul hpos ?_ hφ hφs).2
    · intro f hf hfc hfs
      have hFint : Integrable (fun z : s => f (z : EuclideanSpace ℝ (Fin n))) ν :=
        Continuous.integrable_of_hasCompactSupport (hf.continuous.comp continuous_subtype_val)
          (by
            rw [hasCompactSupport_def]
            have hle : tsupport (fun z : s => f (z : EuclideanSpace ℝ (Fin n)))
                ⊆ Subtype.val ⁻¹' tsupport f :=
              closure_minimal (fun z hz => subset_tsupport f hz)
                ((isClosed_tsupport f).preimage continuous_subtype_val)
            exact (Topology.IsInducing.subtypeVal.isCompact_preimage' hfc.isCompact
              (by simpa [Subtype.range_coe] using hfs)).of_isClosed_subset
              (isClosed_tsupport (fun z : s => f (z : EuclideanSpace ℝ (Fin n)))) hle)
      have hfin : ∫⁻ x, ‖f x‖ₑ ∂μ < ⊤ := by
        rw [hμdef, lintegral_map (hf.continuous.measurable.enorm) measurable_subtype_coe]
        exact hFint.2
      exact ⟨hf.continuous.measurable.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr hfin⟩
    · intro f hf hfc hfs
      have hFmem : toCc f hf.continuous hfc hfs ∈ smoothSub s := by
        change ContDiff ℝ ∞ (zext (toCc f hf.continuous hfc hfs))
        rw [zext_toCc]; exact hf
      have h1 : ∫ x, f x ∂μ = ∫ z, (toCc f hf.continuous hfc hfs) z ∂ν := by
        rw [hμdef, (MeasurableEmbedding.subtype_coe hs.measurableSet).integral_map f]
        rfl
      rw [h1, hνdef]
      simp only [RealRMK.integral_rieszMeasure]
      change g (toCc f hf.continuous hfc hfs) = Λ f
      rw [hgeq ⟨toCc f hf.continuous hfc hfs, hFmem⟩]
      change Λ (zext (toCc f hf.continuous hfc hfs)) = Λ f
      rw [zext_toCc]

end Main
end
end Commons.Measure.Distribution