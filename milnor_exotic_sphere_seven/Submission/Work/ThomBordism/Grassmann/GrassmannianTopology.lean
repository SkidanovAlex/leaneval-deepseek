import Submission.Work.ThomBordism.Grassmann.Grassmannian

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-!
# The oriented Grassmannian is a compact Hausdorff space

`G̃r_k(ℝ^{k+m})` is the quotient of the compact T2 Stiefel manifold `V_k(ℝ^{k+m})` by the action of
`SO(k)`.  This module proves that it is Hausdorff (`instT2SpaceOG`).

The route is the standard one for compact group actions, made explicit:

* `SO(k)` is compact (`instCompactSpaceSOk`): it is closed and bounded in the space of matrices;
* hence the orbit relation `r` is **closed** in `Stiefel × Stiefel`: it is the image of the compact
  space `SO(k) × Stiefel` under the continuous map `(A, f) ↦ (A • f, f)`;
* the **saturations of open sets are open** (`isOpen_saturation`), because the action of `A` is an
  open map (a homeomorphism, with inverse the action of `Aᵀ`);
* a closed equivalence relation on a compact T2 space whose saturated open sets are open has T2
  quotient (`instT2SpaceOG`), the separating open sets being the saturations of a pair of open sets
  whose product misses the relation.
-/

namespace Work.ThomBordism.Grassmann

open scoped Topology Matrix.Norms.Elementwise

noncomputable section

variable {k m : ℕ}

instance instTopologicalSpaceSOk (k : ℕ) : TopologicalSpace (SOk k) :=
  inferInstanceAs (TopologicalSpace {A : Matrix (Fin k) (Fin k) ℝ // IsSO A})

/-! ## `SO(k)` is compact -/

theorem isClosed_isSO :
    IsClosed {A : Matrix (Fin k) (Fin k) ℝ | IsSO A} := by
  have h1 : IsClosed {A : Matrix (Fin k) (Fin k) ℝ | A.transpose * A = 1} := by
    rw [show {A : Matrix (Fin k) (Fin k) ℝ | A.transpose * A = 1}
        = (fun A : Matrix (Fin k) (Fin k) ℝ => A.transpose * A) ⁻¹' {1} from rfl]
    refine isClosed_singleton.preimage ?_
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Set.mem_singleton_iff]
    exact continuous_finset_sum _ fun l _ => (continuous_apply_apply l i).mul
      (continuous_apply_apply l j)
  have h2 : IsClosed {A : Matrix (Fin k) (Fin k) ℝ | A.det = 1} := by
    rw [show {A : Matrix (Fin k) (Fin k) ℝ | A.det = 1} = Matrix.det ⁻¹' {1} from rfl]
    exact isClosed_singleton.preimage (continuous_id (X := Matrix (Fin k) (Fin k) ℝ)).matrix_det
  have : {A : Matrix (Fin k) (Fin k) ℝ | IsSO A}
      = {A : Matrix (Fin k) (Fin k) ℝ | A.transpose * A = 1} ∩ {A | A.det = 1} := rfl
  rw [this]
  exact h1.inter h2

theorem norm_le_one_of_isSO {A : Matrix (Fin k) (Fin k) ℝ} (hA : IsSO A) : ‖A‖ ≤ 1 := by
  rw [Matrix.norm_le_iff zero_le_one]
  intro i j
  have h1 : ∑ l, A l j * A l j = 1 := by
    have h := congrFun (congrFun hA.1 j) j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] using h
  have h2 : A i j * A i j ≤ ∑ l, A l j * A l j :=
    Finset.single_le_sum (fun l _ => mul_self_nonneg (A l j)) (Finset.mem_univ i)
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · nlinarith [h1, h2]
  · nlinarith [h1, h2]

theorem isBounded_isSO : Bornology.IsBounded {A : Matrix (Fin k) (Fin k) ℝ | IsSO A} := by
  rw [isBounded_iff_forall_norm_le]
  exact ⟨1, fun _ hA => norm_le_one_of_isSO hA⟩

instance instCompactSpaceSOk (k : ℕ) : CompactSpace (SOk k) :=
  isCompact_iff_compactSpace.mp
    (Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_isSO, isBounded_isSO⟩)

/-! ## The action is continuous -/

theorem continuous_soActFun :
    Continuous fun p : Matrix (Fin k) (Fin k) ℝ × (Fin k → Amb (k+m)) => soActFun p.1 p.2 := by
  rw [continuous_pi_iff]
  intro i
  simp only [soActFun]
  refine continuous_finset_sum _ fun j _ => ?_
  exact (((continuous_apply i).comp ((continuous_apply j).comp continuous_fst)).smul
    ((continuous_apply j).comp continuous_snd)).congr fun p => by simp

theorem continuous_act (A : SOk k) : Continuous (A.act : Stiefel k m → Stiefel k m) :=
  (continuous_soActFun.comp
    (Continuous.prodMk continuous_const continuous_subtype_val)).subtype_mk _

/-! ## The orbit relation is closed -/

theorem continuous_act_pair :
    Continuous fun q : SOk k × Stiefel k m => q.1.act q.2 := by
  have h : Continuous fun q : SOk k × Stiefel k m => soActFun q.1.1 q.2.1 :=
    continuous_soActFun.comp (Continuous.prodMk
      (continuous_subtype_val.comp continuous_fst) (continuous_subtype_val.comp continuous_snd))
  exact h.subtype_mk _

theorem continuous_orbitPair :
    Continuous fun q : SOk k × Stiefel k m =>
      ((q.2, q.1.act q.2) : Stiefel k m × Stiefel k m) :=
  Continuous.prodMk continuous_snd continuous_act_pair

theorem isClosed_grassmannRel :
    IsClosed {p : Stiefel k m × Stiefel k m | (grassmannSetoid k m).r p.1 p.2} := by
  have hcl : IsClosed (Set.range fun q : SOk k × Stiefel k m =>
      ((q.2, q.1.act q.2) : Stiefel k m × Stiefel k m)) := by
    simpa only [Set.image_univ] using (isCompact_univ.image continuous_orbitPair).isClosed
  have hset : {p : Stiefel k m × Stiefel k m | (grassmannSetoid k m).r p.1 p.2}
      = Set.range fun q : SOk k × Stiefel k m =>
          ((q.2, q.1.act q.2) : Stiefel k m × Stiefel k m) := by
    ext p; constructor
    · rintro ⟨A, hA⟩
      exact ⟨(A, p.1), Prod.ext rfl hA.symm⟩
    · rintro ⟨q, hq⟩
      exact ⟨q.1, by rw [← hq]⟩
  rw [hset]
  exact hcl

/-! ## Saturations of open sets are open -/

theorem act_act_transpose (A : SOk k) (f : Stiefel k m) :
    (A.act : Stiefel k m → Stiefel k m) (A.transpose.act f) = f := by
  have h : A.transpose * A = 1 := Subtype.ext A.2.1
  rw [← SOk.act_mul, h, SOk.act_one]

theorem isOpen_saturation (U : Set (Stiefel k m)) (hU : IsOpen U) :
    IsOpen {f : Stiefel k m | ∃ g ∈ U, (grassmannSetoid k m).r g f} := by
  have h : {f : Stiefel k m | ∃ g ∈ U, (grassmannSetoid k m).r g f}
      = ⋃ A : SOk k, A.act '' U := by
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨g, hg, A, hfg⟩
      exact ⟨A, g, hg, hfg.symm⟩
    · rintro ⟨A, g, hg, hfg⟩
      exact ⟨g, hg, A, hfg.symm⟩
  rw [h]
  refine isOpen_iUnion fun A => ?_
  have hpre : A.act '' U = A.transpose.act ⁻¹' U := by
    ext f; constructor
    · rintro ⟨g, hg, rfl⟩
      show A.transpose.act (A.act g) ∈ U
      rw [SOk.act_transpose_act]; exact hg
    · intro hf
      exact ⟨A.transpose.act f, hf, act_act_transpose A f⟩
  rw [hpre]
  exact hU.preimage (continuous_act A.transpose)

theorem saturation_saturated (U : Set (Stiefel k m)) :
    ∀ {x : Stiefel k m}, x ∈ {f : Stiefel k m | ∃ g ∈ U, (grassmannSetoid k m).r g f} →
      ∀ {y : Stiefel k m}, (grassmannSetoid k m).r x y →
        y ∈ {f : Stiefel k m | ∃ g ∈ U, (grassmannSetoid k m).r g f} := by
  intro x hx y hxy
  obtain ⟨g, hgU, hgx⟩ := hx
  obtain ⟨A, hAx⟩ := hgx
  obtain ⟨B, hBy⟩ := hxy
  refine ⟨g, hgU, A * B, ?_⟩
  rw [hBy, hAx, SOk.act_mul]

/-! ## The quotient is Hausdorff -/

instance instT2SpaceOG (k m : ℕ) : T2Space (OG k m) := by
  refine T2Space.mk ?_
  rintro ⟨f₀⟩ ⟨g₀⟩ hne
  have hnr : ¬ (grassmannSetoid k m).r f₀ g₀ := fun h => hne (Quotient.sound h)
  -- a product of open sets around `(f₀, g₀)` missing the relation
  obtain ⟨U, V, hUo, hVo, hfU, hgV, hUV⟩ : ∃ U V : Set (Stiefel k m),
      IsOpen U ∧ IsOpen V ∧ f₀ ∈ U ∧ g₀ ∈ V ∧ ∀ x ∈ U, ∀ y ∈ V,
        ¬ (grassmannSetoid k m).r x y := by
    have hopen : IsOpen {p : Stiefel k m × Stiefel k m | (grassmannSetoid k m).r p.1 p.2}ᶜ :=
      (isClosed_grassmannRel (k := k) (m := m)).isOpen_compl
    have hmem : (f₀, g₀) ∈ {p : Stiefel k m × Stiefel k m | (grassmannSetoid k m).r p.1 p.2}ᶜ :=
      hnr
    obtain ⟨U, V, hUo, hVo, hfU, hgV, hsub⟩ := isOpen_prod_iff.mp hopen f₀ g₀ hmem
    exact ⟨U, V, hUo, hVo, hfU, hgV,
      fun x hx y hy => by
        have hmem : ((x, y) : Stiefel k m × Stiefel k m) ∈ U ×ˢ V := ⟨hx, hy⟩
        simpa only [Set.mem_compl_iff, Set.mem_setOf_eq] using hsub hmem⟩
  -- the saturated open sets
  set U' := {f : Stiefel k m | ∃ g ∈ U, (grassmannSetoid k m).r g f} with hU'def
  set V' := {f : Stiefel k m | ∃ g ∈ V, (grassmannSetoid k m).r g f} with hV'def
  have hU'o : IsOpen U' := isOpen_saturation U hUo
  have hV'o : IsOpen V' := isOpen_saturation V hVo
  have hdisj : Disjoint U' V' := by
    rw [Set.disjoint_iff]
    rintro z ⟨hzU, hzV⟩
    obtain ⟨x, hxU, hxz⟩ := hzU
    obtain ⟨y, hyV, hyz⟩ := hzV
    obtain ⟨A, hAx⟩ := hxz
    obtain ⟨B, hBy⟩ := hyz
    refine hUV x hxU y hyV ⟨A * B.transpose, ?_⟩
    have h1 : y = (B.transpose).act z := by
      rw [hBy]; exact (SOk.act_transpose_act B y).symm
    rw [h1, hAx, SOk.act_mul]
  refine ⟨Quotient.mk'' '' U', Quotient.mk'' '' V', ?_, ?_, ?_, ?_, ?_⟩
  · -- open in the quotient
    rw [isOpen_coinduced]
    show IsOpen ((Quotient.mk'' : Stiefel k m → OG k m) ⁻¹' (Quotient.mk'' '' U'))
    have hpre : (Quotient.mk'' : Stiefel k m → OG k m) ⁻¹' (Quotient.mk'' '' U') = U' := by
      ext x; constructor
      · rintro ⟨y, hy, hyx⟩
        exact saturation_saturated U hy (Quotient.exact hyx)
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [hpre]; exact hU'o
  · rw [isOpen_coinduced]
    show IsOpen ((Quotient.mk'' : Stiefel k m → OG k m) ⁻¹' (Quotient.mk'' '' V'))
    have hpre : (Quotient.mk'' : Stiefel k m → OG k m) ⁻¹' (Quotient.mk'' '' V') = V' := by
      ext x; constructor
      · rintro ⟨y, hy, hyx⟩
        exact saturation_saturated V hy (Quotient.exact hyx)
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [hpre]; exact hV'o
  · exact ⟨f₀, ⟨f₀, hfU, (grassmannSetoid k m).iseqv.refl f₀⟩, rfl⟩
  · exact ⟨g₀, ⟨g₀, hgV, (grassmannSetoid k m).iseqv.refl g₀⟩, rfl⟩
  · rw [Set.disjoint_iff]
    rintro z ⟨⟨x, hxU', rfl⟩, ⟨y, hyV', hxy⟩⟩
    -- `x ∈ U'` and `y ∈ V'` with `x ≈ y` force `y ∈ U'`
    have hyU' : y ∈ U' := saturation_saturated U hxU' (Quotient.exact hxy.symm)
    exact Set.disjoint_left.mp hdisj hyU' hyV'

end

end Work.ThomBordism.Grassmann
