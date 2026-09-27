import Mathlib
import Submission.Work.Cells.Connell.connell_aux
import Submission.Work.Cells.Connell.Defs
import Submission.Work.PL.Defs
import Submission.Work.Cells.Connell.cubeChart_injOn
import Submission.Work.Cells.Connell.cubeChart_isOpen_image_openCube
import Submission.Work.Cells.Connell.cubeChart_isCompact_image_closedCube
import Submission.Work.Cells.Connell.exists_cubeChart_subcube
import Submission.Work.Cells.Connell.exists_thinFamily_of_domDim
import Submission.Work.Cells.Connell.extOverDisc_of_homeomorph
import Submission.Work.Cells.Connell.cubeChart_homeoOn_apply
import Submission.Work.Cells.Connell.exists_closedCube_of_isCompact_subset_image_openCube

namespace Work.Cells.Connell

open Set Metric

/-- The image under a cube chart of an open subset of the open unit cube is open: the chart
restricts to an open embedding of the open unit cube. -/
theorem isOpen_image_chart_of_isOpen_subset {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : PL.CubeChart n M) {U : Set (PL.E n)} (hU : IsOpen U)
    (hU1 : U ⊆ PL.openCube (n := n) 1) : IsOpen (c.toFun '' U) := by
  have hpre : IsOpen (Subtype.val ⁻¹' U : Set ↥(PL.openCube (n := n) 1)) :=
    hU.preimage continuous_subtype_val
  have heq : c.toFun '' U
      = ((PL.openCube (n := n) 1).domRestrict c.toFun) ''
          (Subtype.val ⁻¹' U : Set ↥(PL.openCube (n := n) 1)) := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hU1 hx⟩, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x.1, hx, rfl⟩
  rw [heq]
  exact c.emb.isOpenMap _ hpre

/-- The identity identifies `{x : ↥A | (x : X) ∈ V}` with `↥V` when `V ⊆ A`. -/
noncomputable def identifySubtypeOfSubset {X : Type*} [TopologicalSpace X] {A V : Set X}
    (hVA : V ⊆ A) : ↥{x : ↥A | (x : X) ∈ V} ≃ₜ ↥V where
  toFun x := ⟨(x : ↥A).1, x.2⟩
  invFun y := ⟨⟨y.1, hVA y.2⟩, y.2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- `PL.ExtOverDisc` passes from `↥V` to the corresponding subset of a larger subtype `↥A`. -/
theorem extOverDisc_of_subset_subtype {X : Type*} [TopologicalSpace X] {A V : Set X}
    (hVA : V ⊆ A) {j : ℕ} (h : PL.ExtOverDisc ↥V j) :
    PL.ExtOverDisc ↥{x : ↥A | (x : X) ∈ V} j :=
  extOverDisc_of_homeomorph (identifySubtypeOfSubset hVA).symm h

theorem engulf_skel {n : ℕ} {M : Type*} [MetricSpace M]
    (A : Assumptions n M) (hloc : PL.LocCube n M)
    (hconn : ∀ j, j + 1 ≤ n → PL.ExtOverDisc M j)
    {cA cC : PL.CubeChart n M} {β₀ β : ℝ}
    (hβ₀0 : 0 < β₀) (hβ₀β : β₀ < β) (hβ1 : β < 1)
    {p : ℕ} (hp : p + 3 ≤ n)
    (T : Set (PL.E n)) (hTcomp : IsCompact T) (hTβ : T ⊆ PL.closedCube (n := n) β)
    (hTdom : PL.DomDim T (p : ℤ)) :
    ∃ HA : M ≃ₜ M,
      cC.toFun '' T ⊆ HA '' (cA.toFun '' PL.openCube (n := n) 1) ∧
      (∀ x : M, x ∈ cA.toFun '' PL.closedCube (n := n) β₀ → HA x = x) := by
  classical
  have hβ₀1 : β₀ < 1 := lt_trans hβ₀β hβ1
  have hn1 : 1 ≤ n := by omega
  -- ------------------------------------------------------------------ objects
  set A₀ : Set M := cA.toFun '' PL.closedCube (n := n) β₀ with hA₀def
  set MA : Set M := A₀ᶜ with hMAdef
  set U : Set (PL.E n) := PL.openCube (n := n) 1 \ PL.closedCube (n := n) β₀ with hUdef
  set V : Set ↥MA := {x : ↥MA | (x : M) ∈ cA.toFun '' U} with hVdef
  set X : Set ↥MA := {x : ↥MA | (x : M) ∈ cC.toFun '' T} with hXdef
  -- ------------------------------------------------------------------ basics
  have hTsub1 : T ⊆ PL.openCube (n := n) 1 :=
    fun x hx => closedCube_subset_openCube_lt_one hβ1 (hTβ hx)
  have hA₀closed : IsClosed A₀ := by
    rw [hA₀def]; exact (cubeChart_isCompact_image_closedCube cA hβ₀1).isClosed
  have hMAopen : IsOpen MA := by rw [hMAdef]; exact hA₀closed.isOpen_compl
  have hUopen : IsOpen U := by
    rw [hUdef]; exact (isOpen_openCube n 1).sdiff (isClosed_closedCube β₀)
  have hUsub : U ⊆ PL.openCube (n := n) 1 := by
    intro x hx; rw [hUdef] at hx; exact hx.1
  have hUnotcl : ∀ x ∈ U, x ∉ PL.closedCube (n := n) β₀ := by
    intro x hx; rw [hUdef] at hx; exact hx.2
  -- a point of the complement of the closed chart cube
  obtain ⟨z₀, hz₀1, hz₀2⟩ := exists_mem_openCube_notMem_closedCube hn1 hβ₀0 hβ₀1
  have hz₀MA : cA.toFun z₀ ∈ MA := by
    rw [hMAdef, hA₀def]
    rintro ⟨t, ht, hteq⟩
    have ht1 : t ∈ PL.openCube (n := n) 1 := closedCube_subset_openCube_lt_one hβ₀1 ht
    have hzt : t = z₀ := cubeChart_injOn cA ht1 hz₀1 hteq
    exact hz₀2 (hzt ▸ ht)
  have hz₀U : z₀ ∈ U := by rw [hUdef]; exact ⟨hz₀1, hz₀2⟩
  have hMAne : (A₀ᶜ).Nonempty := ⟨cA.toFun z₀, hz₀MA⟩
  -- the image of the annulus lies in `MA`
  have hAUsubMA : cA.toFun '' U ⊆ MA := by
    rintro y ⟨u, hu, rfl⟩
    rw [hMAdef, hA₀def]
    rintro ⟨t, ht, hteq⟩
    have ht1 : t ∈ PL.openCube (n := n) 1 := closedCube_subset_openCube_lt_one hβ₀1 ht
    have hut : u = t := cubeChart_injOn cA (hUsub hu) ht1 hteq.symm
    exact hUnotcl u hu (hut.symm ▸ ht)
  -- ------------------------------------------------------------------ the engulf hypotheses
  have hVopen : IsOpen V := by
    rw [hVdef]; exact (isOpen_image_chart_of_isOpen_subset cA hUopen hUsub).preimage
      continuous_subtype_val
  have hVne : V.Nonempty := by
    rw [hVdef]
    exact ⟨⟨cA.toFun z₀, hz₀MA⟩, z₀, hz₀U, rfl⟩
  have hVconn : ∀ j, j + 1 ≤ p → PL.ExtOverDisc ↥V j := by
    intro j hj
    have hj2 : j + 2 ≤ n := by omega
    have hannj : PL.ExtOverDisc ↥U j := A.annulus β₀ hβ₀0 hβ₀1 j hj2
    obtain ⟨e, _he⟩ := cubeChart_homeoOn_apply cA hUopen hUsub
    have himg : PL.ExtOverDisc ↥(cA.toFun '' U) j := extOverDisc_of_homeomorph e hannj
    exact extOverDisc_of_subset_subtype hAUsubMA himg
  have hTimg_compact : IsCompact (cC.toFun '' T) :=
    hTcomp.image_of_continuousOn (cC.cont.mono hTsub1)
  have hTimg_closed : IsClosed (cC.toFun '' T) := hTimg_compact.isClosed
  have hAU1open : IsOpen (cA.toFun '' PL.openCube (n := n) 1) :=
    cubeChart_isOpen_image_openCube cA one_pos le_rfl
  have hXclosed : IsClosed X := by
    rw [hXdef]; exact hTimg_closed.preimage continuous_subtype_val
  have hXcomp : IsCompact (X \ V) := by
    have hKcompact : IsCompact (cC.toFun '' T ∩ (cA.toFun '' PL.openCube (n := n) 1)ᶜ) :=
      hTimg_compact.inter_right hAU1open.isClosed_compl
    have hKsub : cC.toFun '' T ∩ (cA.toFun '' PL.openCube (n := n) 1)ᶜ ⊆ MA := by
      rw [hMAdef, hA₀def]
      intro y hy
      exact fun hcon => hy.2 (Set.image_mono (closedCube_subset_openCube_lt_one hβ₀1) hcon)
    have hιK : IsCompact {x : ↥MA | (x : M) ∈
        (cC.toFun '' T ∩ (cA.toFun '' PL.openCube (n := n) 1)ᶜ)} :=
      isCompact_subtype_preimage_of_subset hKcompact hKsub
    refine IsCompact.of_isClosed_subset hιK (hXclosed.sdiff hVopen) ?_
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [hXdef] at hx; exact hx.1
    · rintro ⟨z, hz1, hzeq⟩
      by_cases hzc : z ∈ PL.closedCube (n := n) β₀
      · exact x.2 ⟨z, hzc, hzeq⟩
      · exact hx.2 (by rw [hVdef]; exact ⟨z, by rw [hUdef]; exact ⟨hz1, hzc⟩, hzeq⟩)
  have hXdom : ∀ x ∈ X, ∃ ψ : PL.CubeChart n ↥MA, x ∈ ψ.toFun '' PL.openCube (1 / 2) ∧
      ∃ Pd : Set (PL.E n), PL.DomDim Pd (p : ℤ) ∧
        ∀ y ∈ PL.closedCube (1 : ℝ), ψ.toFun y ∈ X → y ∈ Pd := by
    intro x hxX
    rw [hXdef] at hxX
    obtain ⟨y₀, hy₀T, hy₀eq⟩ := hxX
    have hy₀1 : y₀ ∈ PL.openCube (n := n) 1 := hTsub1 hy₀T
    have hyA : cC.toFun y₀ ∉ A₀ := by
      rw [hy₀eq]
      have hxMA : (x : M) ∈ A₀ᶜ := by rw [← hMAdef]; exact x.2
      exact hxMA
    -- a point of `A₀ᶜ` missed by `cC '' T`: used as the value of the chart off the open cube
    obtain ⟨ι, hι, F, hFthin, hTF⟩ :=
      exists_thinFamily_of_domDim hTdom hTβ hβ1 (by omega : (p : ℤ) + 1 ≤ (n : ℤ))
    haveI : Finite ι := hι
    obtain ⟨pj, hpjA₀, hpjT⟩ :=
      exists_notMem_image_of_thinFamily' (A := A₀) hA₀closed hMAne cC F hFthin hTF
    obtain ⟨r, hrpos, ψ, hψ1, hψ2, hψ3⟩ :=
      exists_cubeChart_subcube cC y₀ hy₀1 A₀ hA₀closed hyA ⟨pj, hpjA₀⟩
    refine ⟨ψ, ?_, ?_⟩
    · refine ⟨0, ?_, ?_⟩
      · intro i; simp
      · apply Subtype.ext
        rw [hψ1 0 (by intro i; simp)]
        simp [hy₀eq]
    · refine ⟨{z : PL.E n | y₀ + r • z ∈ T}, ?_, ?_⟩
      · have h := A.domDimAffine y₀ r (ne_of_gt hrpos) T (p : ℤ) hTdom
        simpa using h
      · intro y hy hyX
        by_cases hy1 : y ∈ PL.openCube (n := n) 1
        · have hψy : (ψ.toFun y : M) = cC.toFun (y₀ + r • y) := hψ1 y hy1
          rw [hXdef] at hyX
          obtain ⟨t, htT, hteq⟩ := hyX
          have hall : cC.toFun (y₀ + r • y) = cC.toFun t := by rw [← hψy, hteq]
          have hsub1 : y₀ + r • y ∈ PL.openCube (n := n) 1 := (hψ3 y hy).1
          have hyt : y₀ + r • y = t := cubeChart_injOn cC hsub1 (hTsub1 htT) hall
          show y₀ + r • y ∈ T
          rw [hyt]; exact htT
        · exfalso
          have hpy : ψ.toFun y = (⟨pj, hpjA₀⟩ : ↥A₀ᶜ) := hψ2 y hy1
          rw [hXdef] at hyX
          obtain ⟨t, htT, hteq⟩ := hyX
          exact hpjT ⟨t, htT, by rw [hteq, hpy]⟩
  -- ------------------------------------------------------------------ apply engulf
  obtain ⟨h, hsupp, hXeng⟩ :=
    A.engulf p ↥MA hp (A.locCubeOpen M MA hMAopen hloc)
      (fun j hj => A.cubeMinus M cA β₀ hβ₀0 hβ₀1 j (by omega) (hconn j (by omega)))
      V hVopen hVne hVconn X hXclosed hXcomp hXdom
  -- ------------------------------------------------------------------ extend to `M`
  obtain ⟨C, hCcomp, _hCsub, hCid⟩ := hsupp
  obtain ⟨H, hHh, hHid⟩ := A.extHomeo M MA hMAopen h C hCcomp hCid
  refine ⟨H, ?_, ?_⟩
  · intro w hw
    obtain ⟨y₀, hy₀T, hy₀eq⟩ := hw
    by_cases hwMA : w ∈ MA
    · have hxX : (⟨w, hwMA⟩ : ↥MA) ∈ X := by
        rw [hXdef]; exact ⟨y₀, hy₀T, hy₀eq⟩
      obtain ⟨v, hvV, hv_eq⟩ := hXeng hxX
      refine ⟨(v : M), ?_, ?_⟩
      · rw [hVdef] at hvV
        obtain ⟨u, hu, hueq⟩ := hvV
        exact ⟨u, hUsub hu, hueq⟩
      · rw [hHh v, hv_eq]
    · have hwA₀ : w ∈ A₀ := by
        by_contra hc
        exact hwMA (by rw [hMAdef]; exact hc)
      have hwU1 : w ∈ cA.toFun '' PL.openCube (n := n) 1 :=
        Set.image_mono (closedCube_subset_openCube_lt_one hβ₀1) hwA₀
      have hHw : H w = w := hHid w (by rw [hMAdef]; intro hc; exact hc hwA₀)
      exact ⟨w, hwU1, hHw⟩
  · intro x hx
    exact hHid x (by rw [hMAdef]; intro hc; exact hc hx)

end Work.Cells.Connell
