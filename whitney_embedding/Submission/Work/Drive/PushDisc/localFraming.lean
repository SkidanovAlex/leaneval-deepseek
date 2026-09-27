import Mathlib
import Submission.Work.Drive.PushDisc.sheetModel
import Submission.Work.Whitney.CutPush.exists_injective_graphAvoiding

/-!
# The local framing at a double point: the finger can be made a graph fixing the first sheet

`Work.Drive.PushDisc.exists_linearEquiv_fixing_sheetASub` is the **non-degeneracy of the framing at
a transverse double point**.  In the model space `Mdl k = ℝ × ℝ^k × ℝ^k × ℝ^k` the first sheet is
the plane `sheetA = {ξ | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0}` (i.e. `{y = 0, v = 0}`) and the coordinate
plane that the finger's projection must be injective on is
`kerXV k = {ξ | ξ.1 = 0 ∧ ξ.2.2.2 = 0}` (i.e. `{x = 0, v = 0} = span{∂y, ∂u}`, dimension `k + 1 = n`).

For a second sheet through the double point with tangent plane `T` **transverse** to `sheetA`
(`sheetA ⊔ T = ⊤`, the hypothesis `htransP` of the target), the plane `T` need *not* be transverse
to `kerXV` (e.g. `T = span{∂y} ⊕ span{∂v}` with `k = 0`), so the finger is not automatically a graph
over the `(x,v)`-window at the double point.  But the local framing can always be arranged: there is
a linear isomorphism `L` of `Mdl k` which is the **identity on `sheetA` pointwise** (it is the
derivative at the double point of the coordinate change that keeps the first sheet flat) and which
makes `T` transverse to `kerXV k`.

Proof.  `sheetA` and `T` are complementary `(k+1)`-planes.  The general-position engine
`Work.Whitney.CutPush.exists_transverse_of_finrank_le` (PROVED, axiom-clean) produces a `(k+1)`-plane
`K` transverse to both `sheetA` and `kerXV k`; `sheetA` and `K` are then also complementary, and the
projection `↥K → ↥T` along `sheetA` is a linear isomorphism, giving a linear isomorphism
`L : Mdl k ≃ Mdl k` with `L|sheetA = id` and `L '' T = K`.  The conclusion follows from
`K ⊓ kerXV k = ⊥`.
-/

namespace Work.Drive.PushDisc

/-- The coordinate plane `{x = 0, v = 0} = span{∂y, ∂u} ⊆ Mdl k`. -/
def kerXV (k : ℕ) : Submodule ℝ (Work.Drive.Whitney.Mdl k) where
  carrier := {ξ | ξ.1 = 0 ∧ ξ.2.2.2 = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    intro a b ha hb
    exact ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
  smul_mem' := by
    intro c a ha
    exact ⟨by simp [ha.1], by simp [ha.2]⟩

theorem mem_kerXV {k : ℕ} {ξ : Work.Drive.Whitney.Mdl k} :
    ξ ∈ kerXV k ↔ ξ.1 = 0 ∧ ξ.2.2.2 = 0 := Iff.rfl

/-- `kerXV k` has dimension `k + 1` (it is `ℝ × ℝ^k` in the coordinates `(y,u)`). -/
theorem finrank_kerXV (k : ℕ) : Module.finrank ℝ (kerXV k) = k + 1 := by
  let f : Work.Drive.Whitney.Mdl k →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin k)) :=
    (LinearMap.fst ℝ ℝ (ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)))).prod
      ((LinearMap.snd ℝ (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))).comp
        ((LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))).comp
          (LinearMap.snd ℝ ℝ
            (ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))))))
  have hker : kerXV k = LinearMap.ker f := by
    ext ξ
    rw [mem_kerXV, LinearMap.mem_ker]
    constructor
    · rintro ⟨h1, h2⟩
      exact Prod.ext h1 h2
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have hrange : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨a, w⟩
    exact ⟨(a, 0, 0, w), rfl⟩
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, finrank_top, finrank_Mdl, Module.finrank_prod, finrank_euclideanSpace,
    Fintype.card_fin, Module.finrank_self] at h
  rw [hker]
  omega

/-- **The local framing at a transverse double point.**  For `(k+1)`-planes `T` (transverse to the
model first sheet `sheetA`) and `Q` there is a linear isomorphism of the model space which fixes
`sheetA` pointwise and makes `T` transverse to `Q`. -/
theorem exists_linearEquiv_fixing_sheetASub {k : ℕ}
    (T Q : Submodule ℝ (Work.Drive.Whitney.Mdl k))
    (hT : Module.finrank ℝ T = k + 1) (hQ : Module.finrank ℝ Q = k + 1)
    (hsup : sheetASub k ⊔ T = ⊤) :
    ∃ L : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] Work.Drive.Whitney.Mdl k,
      (∀ a ∈ sheetASub k, L a = a) ∧ ∀ t ∈ T, L t ∈ Q → t = 0 := by
  have hdimV : Module.finrank ℝ (Work.Drive.Whitney.Mdl k) = 2 * (k + 1) := finrank_Mdl k
  have hA : Module.finrank ℝ (sheetASub k) = k + 1 := finrank_sheetASub k
  have hinf : sheetASub k ⊓ T = ⊥ := by
    refine Submodule.finrank_eq_zero.mp ?_
    have h := Submodule.finrank_sup_add_finrank_inf_eq (sheetASub k) T
    rw [hsup, finrank_top, hdimV, hA, hT] at h
    omega
  have hcompl : IsCompl (sheetASub k) T :=
    ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩
  -- the general-position engine
  have hSle : ∀ L ∈ ({sheetASub k, Q} : Finset (Submodule ℝ (Work.Drive.Whitney.Mdl k))),
      Module.finrank ℝ ↥L ≤ k + 1 := by
    intro L hL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl
    · exact le_of_eq hA
    · exact le_of_eq hQ
  obtain ⟨K, hKdim0, hKdisj⟩ :=
    Work.Whitney.CutPush.exists_transverse_of_finrank_le (k + 1) (k + 1)
      ({sheetASub k, Q} : Finset (Submodule ℝ (Work.Drive.Whitney.Mdl k)))
      ⟨sheetASub k, by simp⟩ (by rw [hdimV]; omega) hSle
  have hKdim : Module.finrank ℝ K = k + 1 := by rw [hKdim0]; omega
  have hKA : K ⊓ sheetASub k = ⊥ := hKdisj _ (by simp)
  have hKQ : K ⊓ Q = ⊥ := hKdisj _ (by simp)
  have hAK : IsCompl (sheetASub k) K := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff, inf_comm]; exact hKA
    · rw [codisjoint_iff]
      refine Submodule.eq_top_of_finrank_eq ?_
      have h := Submodule.finrank_sup_add_finrank_inf_eq (sheetASub k) K
      rw [inf_comm, hKA, finrank_bot, add_zero, hA, hKdim] at h
      rw [h, hdimV]
      ring
  -- the projection `K → T` along the first sheet is an isomorphism
  have hproj_inj : Function.Injective
      ((T.projectionOnto (sheetASub k) hcompl.symm).comp K.subtype) := by
    intro x y hxy
    have hxy' : (T.projectionOnto (sheetASub k) hcompl.symm) ((x : ↥K) : Work.Drive.Whitney.Mdl k)
        = (T.projectionOnto (sheetASub k) hcompl.symm)
            ((y : ↥K) : Work.Drive.Whitney.Mdl k) := hxy
    have hker : ((x : ↥K) : Work.Drive.Whitney.Mdl k) - ((y : ↥K) : Work.Drive.Whitney.Mdl k)
        ∈ LinearMap.ker (T.projectionOnto (sheetASub k) hcompl.symm) := by
      rw [LinearMap.mem_ker, map_sub, hxy', sub_self]
    rw [Submodule.ker_projectionOnto] at hker
    have hmem : ((x : ↥K) : Work.Drive.Whitney.Mdl k) - ((y : ↥K) : Work.Drive.Whitney.Mdl k)
        ∈ K ⊓ sheetASub k :=
      ⟨sub_mem (Submodule.coe_mem x) (Submodule.coe_mem y), hker⟩
    rw [hKA] at hmem
    exact Subtype.ext (sub_eq_zero.mp hmem)
  have hproj_surj : Function.Surjective
      ((T.projectionOnto (sheetASub k) hcompl.symm).comp K.subtype) := by
    have hrange : LinearMap.range ((T.projectionOnto (sheetASub k) hcompl.symm).comp K.subtype)
        = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      have h := LinearMap.finrank_range_add_finrank_ker
        ((T.projectionOnto (sheetASub k) hcompl.symm).comp K.subtype)
      rw [LinearMap.ker_eq_bot.mpr hproj_inj, finrank_bot, add_zero] at h
      rw [h, hKdim, hT]
    intro y
    have : y ∈ LinearMap.range ((T.projectionOnto (sheetASub k) hcompl.symm).comp K.subtype) := by
      rw [hrange]; exact Submodule.mem_top
    exact this
  let g : ↥T ≃ₗ[ℝ] ↥K :=
    (LinearEquiv.ofBijective ((T.projectionOnto (sheetASub k) hcompl.symm).comp K.subtype)
      ⟨hproj_inj, hproj_surj⟩).symm
  refine ⟨(Submodule.prodEquivOfIsCompl (sheetASub k) T hcompl).symm.trans
    (((LinearEquiv.refl ℝ ↥(sheetASub k)).prodCongr g).trans
      (Submodule.prodEquivOfIsCompl (sheetASub k) K hAK)), ?_, ?_⟩
  · intro a ha
    have h1 : (Submodule.prodEquivOfIsCompl (sheetASub k) T hcompl).symm a
        = ((⟨a, ha⟩ : ↥(sheetASub k)), 0) := by
      rw [LinearEquiv.symm_apply_eq, Submodule.coe_prodEquivOfIsCompl']
      simp
    simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, h1, map_zero,
      Submodule.coe_prodEquivOfIsCompl']
    simp
  · intro t ht hker
    have hLt : ((Submodule.prodEquivOfIsCompl (sheetASub k) T hcompl).symm.trans
        (((LinearEquiv.refl ℝ ↥(sheetASub k)).prodCongr g).trans
          (Submodule.prodEquivOfIsCompl (sheetASub k) K hAK)) t : Work.Drive.Whitney.Mdl k)
        = (g ⟨t, ht⟩ : ↥K) := by
      have h1 : (Submodule.prodEquivOfIsCompl (sheetASub k) T hcompl).symm t
          = (0, (⟨t, ht⟩ : ↥T)) := by
        rw [LinearEquiv.symm_apply_eq, Submodule.coe_prodEquivOfIsCompl']
        simp
      simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, h1,
        Submodule.coe_prodEquivOfIsCompl']
      simp
    have hmem : ((g ⟨t, ht⟩ : ↥K) : Work.Drive.Whitney.Mdl k) ∈ K ⊓ Q :=
      ⟨Submodule.coe_mem (g ⟨t, ht⟩), by rw [← hLt]; exact hker⟩
    rw [hKQ, Submodule.mem_bot] at hmem
    have h4 : g ⟨t, ht⟩ = 0 := Subtype.coe_injective hmem
    have h2 : (⟨t, ht⟩ : ↥T) = 0 := by
      have h3 := congrArg (fun x : ↥K => (g.symm x : ↥T)) h4
      simpa using h3
    exact Subtype.ext_iff.mp h2

/-- **The concrete form**: the finger at a double point can be made a graph over the `(x,v)`-window
while the first sheet stays fixed. -/
theorem exists_linearEquiv_fixing_sheetASub_kerXV {k : ℕ}
    (T : Submodule ℝ (Work.Drive.Whitney.Mdl k))
    (hT : Module.finrank ℝ T = k + 1) (hsup : sheetASub k ⊔ T = ⊤) :
    ∃ L : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] Work.Drive.Whitney.Mdl k,
      (∀ a ∈ sheetASub k, L a = a) ∧ ∀ t ∈ T, L t ∈ kerXV k → t = 0 :=
  exists_linearEquiv_fixing_sheetASub T (kerXV k) hT (finrank_kerXV k) hsup

end Work.Drive.PushDisc
