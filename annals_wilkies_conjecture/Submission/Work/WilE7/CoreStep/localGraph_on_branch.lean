/-
  `Work.WilE7.CoreStep.localGraph_on_branch`: **a `Good` absolute stratum of full projection rank
  is, near any of its points, the graph of a continuous function over its `π_n`-projection.**

  Statement: for `T : Stratum 0 (n+q)` with `T.Good`, with `projRank T z = n + q - T.j` at every
  point `z ∈ T.X.set`, and for `z ∈ T.X.set`, there are `V ∈ 𝓝 (absPt z)` and
  `g : ℝ^n → ℝ^q` such that

  * `g` is continuous on `π_n (absSet T ∩ V)`,
  * `x ↦ Fin.append x (g x)` maps `π_n (absSet T ∩ V)` back into `absSet T ∩ V`,
  * `g (π_n w) = projSnd w` for every `w ∈ absSet T ∩ V`.

  ## Mathematics

  The hypothesis `hrank` says that the linear map
  `P := basePrLin n q ↾ ker (jac T z) : ker (jac T z) → ℝ^n`
  is injective (equivalently, the rank `n + q - T.j` of its image equals `dim ker (jac T z)`),
  see `basePrLin_injective_on_ker_jac`.  Consequently the map

  `β : ℝ^{0+(n+q)} → ℝ^n × ℝ^{T.j}`,  `β w = (basePrLin n q w, eqMap T w)`,

  is an *immersion* at `z`: its strict derivative `ζ' : w ↦ (basePrLin n q w, fderiv (eqMap T) z w)`
  is injective (a vector killed by `ζ'` lies in `ker (jac T z)` with vanishing base coordinates,
  hence is zero).  Any injective continuous linear map between finite-dimensional spaces has a
  continuous linear left inverse `Q`, and `localEmbedding_of_injective_strictFDeriv` (the local
  inverse function theorem for an injective strict derivative, proved via
  `HasStrictFDerivAt.toOpenPartialHomeomorph` applied to `Q ∘ β`) then produces `W ∈ 𝓝 z` and
  `r : ℝ^n × ℝ^{T.j} → ℝ^{0+(n+q)}` with

  `ContinuousOn r (β '' W)`  and  `r (β w) = w`  for all `w ∈ W`.

  Since points of the stratum have `eqMap T w = 0` (`T.Good`), we have `β w = (basePrLin n q w, 0)`
  for `w ∈ T.X.set`, so on the stratum `r` *is* the inverse of `basePrLin n q`; the graph function
  is therefore

  `g x := projSnd n q (absPt (r (x, 0)))`,

  which is continuous on `basePrLin n q '' (T.X.set ∩ W)` (the image of `x ↦ (x, 0)`) and satisfies
  `g (basePrLin n q w) = projSnd n q (absPt w)` for `w ∈ T.X.set ∩ W`.  The neighbourhood in the
  statement is `V := absPt '' W ∈ 𝓝 (absPt z)`, and `absSet T ∩ V = absPt '' (T.X.set ∩ W)`, with
  `π_n (absSet T ∩ V) = basePrLin n q '' (T.X.set ∩ W)` because `projFirst n q ∘ absPt` is
  `basePrLin n q` (`projFirst_absPt_eq_basePrLin`).
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.absGood_locality
import Submission.Work.WilE7.DimAPI.ProjRankAux
import Submission.Work.WilE7.DimAPI.jac_eq_fderiv
import Submission.Work.WilE7.projFirst_fiberClosure
import Submission.Work.WilE7.CoreStep.localEmbedding_of_injective_strictFDeriv
import Submission.Work.WilE7.CoreStep.basePrLin_injective_on_ker_jac

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7.CoreStep

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

/-- The first `n` coordinates of `absPt w` are the base coordinates `basePrLin n q w`. -/
lemma projFirst_absPt_eq_basePrLin {n q : ℕ} (w : Fin (0 + (n + q)) → ℝ) :
    WilkiesDesign.E.projFirst n q (Work.WilE7.MainDesign.absPt w)
      = Work.WilE7.MainDesign.basePrLin n q w := rfl

theorem localGraph_on_branch {n q : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + q))
    (hT : T.Good)
    (hrank : ∀ z ∈ T.X.set, Work.WilE7.MainDesign.projRank T z = n + q - T.j)
    (z : Fin (0 + (n + q)) → ℝ) (hz : z ∈ T.X.set) :
    ∃ V ∈ nhds (Work.WilE7.MainDesign.absPt z), ∃ g : (Fin n → ℝ) → (Fin q → ℝ),
      ContinuousOn g (WilkiesDesign.E.projFirst n q '' (Work.WilE7.MainDesign.absSet T ∩ V)) ∧
      (∀ x ∈ WilkiesDesign.E.projFirst n q '' (Work.WilE7.MainDesign.absSet T ∩ V),
        Fin.append x (g x) ∈ Work.WilE7.MainDesign.absSet T ∩ V) ∧
      (∀ w ∈ Work.WilE7.MainDesign.absSet T ∩ V,
        g (WilkiesDesign.E.projFirst n q w) = WilkiesDesign.E.projSnd n q w) := by
  classical
  -- the pointwise form of `basePrLin_injective_on_ker_jac`
  have hker_inj : ∀ w ∈ LinearMap.ker (Work.WilE7.MainDesign.jac T z),
      Work.WilE7.MainDesign.basePrLin n q w = 0 → w = 0 := by
    intro w hw hw0
    have h := basePrLin_injective_on_ker_jac T hT z hz (hrank z hz)
      (a₁ := ⟨w, hw⟩) (a₂ := (0 : ↥(LinearMap.ker (Work.WilE7.MainDesign.jac T z)))) ?_
    · exact congrArg Subtype.val h
    · show Work.WilE7.MainDesign.basePrLin n q w
        = Work.WilE7.MainDesign.basePrLin n q
            ((0 : ↥(LinearMap.ker (Work.WilE7.MainDesign.jac T z))).val)
      rw [hw0]
      rfl
  -- the graph map `β = (basePrLin, eqMap)`, its strict derivative at `z` and its injectivity
  set β : (Fin (0 + (n + q)) → ℝ) → (Fin n → ℝ) × (Fin T.j → ℝ) :=
    fun w => (Work.WilE7.MainDesign.basePrLin n q w, Work.WilE7.DimAPI.eqMap T w) with hβdef
  set ζ' : (Fin (0 + (n + q)) → ℝ) →L[ℝ] (Fin n → ℝ) × (Fin T.j → ℝ) :=
    ((Work.WilE7.MainDesign.basePrLin n q).toContinuousLinearMap).prod
      (fderiv ℝ (Work.WilE7.DimAPI.eqMap T) z) with hζ'def
  have hβstrict : HasStrictFDerivAt β ζ' z := by
    rw [hβdef, hζ'def]
    exact (ContinuousLinearMap.hasStrictFDerivAt
        ((Work.WilE7.MainDesign.basePrLin n q).toContinuousLinearMap)).prodMk
      (Work.WilE7.DimAPI.analyticAt_eqMap T z).hasStrictFDerivAt
  have hζ'apply : ∀ w, ζ' w = (Work.WilE7.MainDesign.basePrLin n q w,
      (fderiv ℝ (Work.WilE7.DimAPI.eqMap T) z) w) := by
    intro w
    rw [hζ'def, ContinuousLinearMap.prod_apply]
    rfl
  have hβinj : Function.Injective ζ' := by
    intro u v huv
    have huv2 : (Work.WilE7.MainDesign.basePrLin n q u,
          (fderiv ℝ (Work.WilE7.DimAPI.eqMap T) z) u)
        = (Work.WilE7.MainDesign.basePrLin n q v,
          (fderiv ℝ (Work.WilE7.DimAPI.eqMap T) z) v) := by
      rw [← hζ'apply u, ← hζ'apply v]; exact huv
    have hfst : Work.WilE7.MainDesign.basePrLin n q u
        = Work.WilE7.MainDesign.basePrLin n q v := congrArg Prod.fst huv2
    have hsnd : (fderiv ℝ (Work.WilE7.DimAPI.eqMap T) z) u
        = (fderiv ℝ (Work.WilE7.DimAPI.eqMap T) z) v := congrArg Prod.snd huv2
    have h1 : Work.WilE7.MainDesign.basePrLin n q (u - v) = 0 := by
      rw [map_sub, hfst, sub_self]
    have h4 : (fderiv ℝ (Work.WilE7.DimAPI.eqMap T) z) (u - v) = 0 := by
      rw [map_sub, hsnd, sub_self]
    have h3 : u - v ∈ LinearMap.ker (Work.WilE7.MainDesign.jac T z) := by
      rw [Work.WilE7.DimAPI.jac_eq_fderiv T z]
      exact h4
    exact sub_eq_zero.mp (hker_inj (u - v) h3 h1)
  -- a continuous linear left inverse of `ζ'`
  obtain ⟨Q, hQ⟩ : ∃ Q : (Fin n → ℝ) × (Fin T.j → ℝ) →L[ℝ] (Fin (0 + (n + q)) → ℝ),
      Q.comp ζ' = ContinuousLinearMap.id ℝ (Fin (0 + (n + q)) → ℝ) := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
      ((ζ' : (Fin (0 + (n + q)) → ℝ) →L[ℝ] (Fin n → ℝ) × (Fin T.j → ℝ)) :
        (Fin (0 + (n + q)) → ℝ) →ₗ[ℝ] (Fin n → ℝ) × (Fin T.j → ℝ))
      (LinearMap.ker_eq_bot.mpr hβinj)
    refine ⟨g.toContinuousLinearMap, ?_⟩
    ext w x
    have h := LinearMap.congr_fun hg w
    simpa [LinearMap.comp_apply] using congrFun h x
  -- the local embedding: `r` inverts `β` near `z`
  obtain ⟨W, hWmem, r, hrcont, hr⟩ :=
    localEmbedding_of_injective_strictFDeriv β ζ' z hβstrict Q hQ
  have hWβ : ∀ w ∈ T.X.set, β w = (Work.WilE7.MainDesign.basePrLin n q w, (0 : Fin T.j → ℝ)) := by
    intro w hw
    rw [hβdef]
    simp only [Work.WilE7.DimAPI.eqMap_eq_zero_of_good T hT hw]
  have hkey : ∀ w ∈ T.X.set ∩ W,
      r (Work.WilE7.MainDesign.basePrLin n q w, (0 : Fin T.j → ℝ)) = w := by
    intro w hw
    rw [← hWβ w hw.1]
    exact hr w hw.2
  -- the neighbourhood `V = absPt '' W` of `absPt z`
  have hVmem : Work.WilE7.MainDesign.absPt '' W ∈ nhds (Work.WilE7.MainDesign.absPt z) := by
    have hcontInv : Continuous (Work.WilE7.DimAPI.absPtInv (n + q)) := by
      refine continuous_pi fun i => ?_
      exact continuous_apply (Fin.cast (Nat.zero_add (n + q)) i)
    obtain ⟨W', hW'sub, hW'open, hzW'⟩ := mem_nhds_iff.mp hWmem
    have hmem : Work.WilE7.DimAPI.absPtInv (n + q) ⁻¹' W'
        ∈ nhds (Work.WilE7.MainDesign.absPt z) := by
      refine hcontInv.continuousAt.preimage_mem_nhds ?_
      rw [Work.WilE7.DimAPI.absPtInv_absPt]
      exact hW'open.mem_nhds hzW'
    refine Filter.mem_of_superset hmem ?_
    intro y hy
    exact ⟨Work.WilE7.DimAPI.absPtInv (n + q) y, hW'sub hy,
      Work.WilE7.DimAPI.absPt_absPtInv (n + q) y⟩
  have hAbs : Work.WilE7.MainDesign.absSet T ∩ (Work.WilE7.MainDesign.absPt '' W)
      = Work.WilE7.MainDesign.absPt '' (T.X.set ∩ W) := by
    rw [Work.WilE7.MainDesign.absSet,
      ← Set.image_inter (Work.WilE7.DimAPI.absPt_injective (n + q))]
  have hSetId : WilkiesDesign.E.projFirst n q ''
        (Work.WilE7.MainDesign.absSet T ∩ (Work.WilE7.MainDesign.absPt '' W))
      = Work.WilE7.MainDesign.basePrLin n q '' (T.X.set ∩ W) := by
    rw [hAbs, Set.image_image]
    rw [show (fun x : Fin (0 + (n + q)) → ℝ =>
          WilkiesDesign.E.projFirst n q (Work.WilE7.MainDesign.absPt x))
        = ⇑(Work.WilE7.MainDesign.basePrLin n q) from
          funext fun x => projFirst_absPt_eq_basePrLin x]
  -- the graph function
  have hsndc : Continuous fun w : Fin (0 + (n + q)) → ℝ =>
      WilkiesDesign.E.projSnd n q (Work.WilE7.MainDesign.absPt w) := by
    have habs : Continuous (Work.WilE7.MainDesign.absPt (N := n + q)) := by
      have h : (fun z : Fin (0 + (n + q)) → ℝ => Work.WilE7.DimAPI.absPtCLM (n + q) z)
          = Work.WilE7.MainDesign.absPt (N := n + q) :=
        funext fun z => Work.WilE7.DimAPI.absPtCLM_apply z
      rw [← h]
      exact (Work.WilE7.DimAPI.absPtCLM (n + q)).continuous
    exact (continuous_pi fun i => continuous_apply (Fin.natAdd n i)).comp habs
  set g : (Fin n → ℝ) → (Fin q → ℝ) :=
    fun x => WilkiesDesign.E.projSnd n q
      (Work.WilE7.MainDesign.absPt (r (x, (0 : Fin T.j → ℝ)))) with hgdef
  have hcont : ContinuousOn g (Work.WilE7.MainDesign.basePrLin n q '' (T.X.set ∩ W)) := by
    have hmaps : ∀ x ∈ Work.WilE7.MainDesign.basePrLin n q '' (T.X.set ∩ W),
        (x, (0 : Fin T.j → ℝ)) ∈ β '' W := by
      rintro x ⟨w, hw, rfl⟩
      exact ⟨w, hw.2, hWβ w hw.1⟩
    have h1 : ContinuousOn (fun x : Fin n → ℝ => r (x, (0 : Fin T.j → ℝ)))
        (Work.WilE7.MainDesign.basePrLin n q '' (T.X.set ∩ W)) :=
      hrcont.comp
        (continuous_id.prodMk (continuous_const : Continuous fun _ : Fin n → ℝ =>
          (0 : Fin T.j → ℝ))).continuousOn
        (fun x hx => hmaps x hx)
    rw [hgdef]
    exact (hsndc.continuousOn (s := Set.univ)).comp h1 (fun x _ => trivial)
  refine ⟨Work.WilE7.MainDesign.absPt '' W, hVmem, g, ?_, ?_, ?_⟩
  · rw [hSetId]; exact hcont
  · intro x hx
    rw [hSetId] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    have hx' : x = WilkiesDesign.E.projFirst n q (Work.WilE7.MainDesign.absPt w) := by
      rw [← hwx, ← projFirst_absPt_eq_basePrLin w]
    have hpres : Fin.append x (WilkiesDesign.E.projSnd n q (Work.WilE7.MainDesign.absPt w))
        = Work.WilE7.MainDesign.absPt w := by
      rw [hx', Work.WilE7.append_projFirst_projSnd]
    have hgx : g x = WilkiesDesign.E.projSnd n q (Work.WilE7.MainDesign.absPt w) := by
      rw [hgdef]
      show WilkiesDesign.E.projSnd n q (Work.WilE7.MainDesign.absPt
          (r (x, (0 : Fin T.j → ℝ))))
        = WilkiesDesign.E.projSnd n q (Work.WilE7.MainDesign.absPt w)
      rw [← hwx, hkey w hw]
    rw [hgx, hpres]
    exact ⟨Set.mem_image_of_mem Work.WilE7.MainDesign.absPt hw.1,
      Set.mem_image_of_mem Work.WilE7.MainDesign.absPt hw.2⟩
  · intro u hu
    obtain ⟨w, hwT, hweq⟩ := hu.1
    have hwW : w ∈ W := by
      obtain ⟨w₂, hw₂, hw₂eq⟩ := hu.2
      have : w₂ = w :=
        Work.WilE7.DimAPI.absPt_injective (n + q) (hw₂eq.trans hweq.symm)
      rw [← this]
      exact hw₂
    have hpf : WilkiesDesign.E.projFirst n q u
        = Work.WilE7.MainDesign.basePrLin n q w := by
      rw [← hweq]
      exact projFirst_absPt_eq_basePrLin w
    show g (WilkiesDesign.E.projFirst n q u) = WilkiesDesign.E.projSnd n q u
    rw [hpf, hgdef]
    show WilkiesDesign.E.projSnd n q (Work.WilE7.MainDesign.absPt
        (r (Work.WilE7.MainDesign.basePrLin n q w, (0 : Fin T.j → ℝ))))
      = WilkiesDesign.E.projSnd n q u
    rw [hkey w ⟨hwT, hwW⟩, hweq]

end Work.WilE7.CoreStep
