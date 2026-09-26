import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.janiszewskiConnectedInter
import Submission.Work.Smooth.SphereJordan.mobiusAddInv
import Submission.Work.Smooth.SphereJordan.Transport

namespace Work.Smooth.SphereJordan

open Set
open scoped OnePoint _root_.Topology

noncomputable section

/-! ## Elementary connectedness helpers -/

/-- If an open set `U` is covered by two disjoint open sets, and two points of `U` lie one in each
of them, they are in different connected components of `U`. -/
theorem notMem_connectedComponentIn_of_separating {α : Type*} [TopologicalSpace α]
    {U X X' : Set α} (hXo : IsOpen X) (hX'o : IsOpen X') (hcover : U ⊆ X ∪ X')
    (hdisj : Disjoint X X') {a b : α} (haU : a ∈ U) (haX : a ∈ X) (hbX' : b ∈ X') :
    b ∉ connectedComponentIn U a := by
  intro hb
  have hpre := isPreconnected_connectedComponentIn (F := U) (x := a)
  have hsub : connectedComponentIn U a ⊆ X ∪ X' := (connectedComponentIn_subset U a).trans hcover
  have hdisj' : connectedComponentIn U a ∩ (X ∩ X') = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro p ⟨-, hpX, hpX'⟩
    exact Set.disjoint_left.mp hdisj hpX hpX'
  rcases (isPreconnected_iff_subset_of_disjoint.mp hpre) X X' hXo hX'o hsub hdisj' with h | h
  · exact Set.disjoint_left.mp hdisj (h hb) hbX'
  · exact Set.disjoint_left.mp hdisj haX (h (mem_connectedComponentIn haU))

/-- The far region `{z : ℂ | r < ‖z‖}` of the plane is preconnected (for `0 ≤ r`). -/
theorem isPreconnected_lt_norm (r : ℝ) (hr : 0 ≤ r) :
    IsPreconnected {z : ℂ | r < ‖z‖} := by
  have hsph : IsPreconnected (Metric.sphere (0 : ℂ) 1) :=
    isPreconnected_sphere (E := ℂ) (by rw [Complex.rank_real_complex]; norm_num) 0 1
  have hprod : IsPreconnected (Set.Ioi r ×ˢ Metric.sphere (0 : ℂ) 1) :=
    isPreconnected_Ioi.prod hsph
  have himg : IsPreconnected
      ((fun p : ℝ × ℂ => p.1 • p.2) '' (Set.Ioi r ×ˢ Metric.sphere (0 : ℂ) 1)) :=
    hprod.image _ (by fun_prop)
  have heq : (fun p : ℝ × ℂ => p.1 • p.2) '' (Set.Ioi r ×ˢ Metric.sphere (0 : ℂ) 1)
      = {z : ℂ | r < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨⟨a, u⟩, ⟨ha, hu⟩, rfl⟩
      have hu' : ‖u‖ = 1 := by
        rw [mem_sphere_iff_norm] at hu; simpa using hu
      show r < ‖a • u‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt hr ha), hu', mul_one]
      exact ha
    · intro hz
      have hzpos : 0 < ‖z‖ := lt_of_le_of_lt hr hz
      refine ⟨(‖z‖, (‖z‖ : ℝ)⁻¹ • z), ⟨hz, ?_⟩, ?_⟩
      · rw [mem_sphere_iff_norm]
        show ‖(‖z‖ : ℝ)⁻¹ • z - 0‖ = 1
        rw [sub_zero, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)), inv_mul_cancel₀ (ne_of_gt hzpos)]
      · show ‖z‖ • ((‖z‖ : ℝ)⁻¹ • z) = z
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hzpos), one_smul]
  rwa [heq] at himg

/-- The frontier of a connected component of the complement of a closed set lies in that set. -/
theorem frontier_connectedComponentIn_subset {A : Set ℂ} (hA : IsClosed A) (z : ℂ) :
    frontier (connectedComponentIn Aᶜ z) ⊆ A := by
  intro q hq
  by_contra hqA
  have hqAc : q ∈ Aᶜ := hqA
  set P : Set ℂ := connectedComponentIn Aᶜ z with hP
  have hPopen : IsOpen P := by rw [hP]; exact hA.isOpen_compl.connectedComponentIn
  have hqclP : q ∈ closure P := frontier_subset_closure hq
  have hqP : q ∉ P := by
    have h := hq
    rw [hPopen.frontier_eq] at h
    exact h.2
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hA.isOpen_compl q hqAc
  obtain ⟨q', hq'P, hq'ball⟩ := Metric.mem_closure_iff.mp hqclP (ε / 2) (by linarith)
  have hball : Metric.ball q ε ⊆ connectedComponentIn Aᶜ q' :=
    IsPreconnected.subset_connectedComponentIn (convex_ball q ε).isPreconnected
      (Metric.mem_ball.mpr (by rw [dist_comm]; linarith)) (fun w hw => hεsub hw)
  have hq'mem : q ∈ connectedComponentIn Aᶜ q' := hball (Metric.mem_ball_self hε)
  have hqeq : connectedComponentIn Aᶜ q' = P :=
    (connectedComponentIn_eq (by rw [← hP]; exact hq'P)).symm.trans hP.symm
  exact hqP (by rwa [hqeq] at hq'mem)

/-- **Comparison of the connected components of the complement of a compact plane set, in the plane
and in the Riemann sphere.**

If `A ⊆ ℂ` is compact and `z, w ∈ ℂ`, then `w` lies in the connected component of `z` in the
complement of `A` *in the Riemann sphere* if and only if it lies in the connected component of `z`
in the complement of `A` *in the plane*.  (The point `∞` glues only the unbounded component of the
plane complement to itself, so it never glues two distinct plane components.) -/
theorem connectedComponentIn_compl_coe {A : Set ℂ} (hA : IsCompact A) (z : ℂ) :
    {w : ℂ | (w : RiemannSphere) ∈ connectedComponentIn ((↑) '' A)ᶜ (z : RiemannSphere)}
      = connectedComponentIn (Aᶜ : Set ℂ) z := by
  have hAcl : IsClosed A := hA.isClosed
  have hAclo : IsOpen (Aᶜ : Set ℂ) := hAcl.isOpen_compl
  set P : Set ℂ := connectedComponentIn Aᶜ z with hP
  have hPopen : IsOpen P := by rw [hP]; exact hAclo.connectedComponentIn
  have hPpre : IsPreconnected P := by rw [hP]; exact isPreconnected_connectedComponentIn
  have hfront : frontier P ⊆ A := by rw [hP]; exact frontier_connectedComponentIn_subset hAcl z
  -- `Aᶜ \ P` is open in the plane
  have hQPopen : IsOpen (Aᶜ \ P) := by
    rw [isOpen_iff_mem_nhds]
    rintro q ⟨hqAc, hqP⟩
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hAclo q hqAc
    refine Filter.mem_of_superset (Metric.ball_mem_nhds q hε) (fun c hc => ⟨hεsub hc, ?_⟩)
    intro hcP
    have hball : Metric.ball q ε ⊆ P := by
      have h1 : Metric.ball q ε ⊆ connectedComponentIn Aᶜ c :=
        IsPreconnected.subset_connectedComponentIn (convex_ball q ε).isPreconnected
          hc (fun u hu => hεsub hu)
      have h2 : connectedComponentIn Aᶜ c = P :=
        (connectedComponentIn_eq (show c ∈ connectedComponentIn Aᶜ z by rw [← hP]; exact hcP)).symm.trans hP.symm
      rw [h2] at h1
      exact h1
    exact hqP (hball (Metric.mem_ball_self hε))
  -- boundedness datum
  obtain ⟨C, hC⟩ := hA.isBounded.exists_norm_le
  have hfar : ({w : ℂ | max C 0 < ‖w‖}) ⊆ Aᶜ := by
    intro w hw
    rw [mem_compl_iff]; intro hwA
    have h1 : ‖w‖ ≤ C := hC w hwA
    have h2 : C ≤ max C 0 := le_max_left _ _
    exact absurd (le_trans h1 h2) (not_le.mpr hw)
  refine Set.Subset.antisymm ?_ ?_
  · -- the hard direction: a sphere-connection is a plane-connection
    intro w hw
    by_contra hwP
    have hwU : (w : RiemannSphere) ∈ ((↑) '' A)ᶜ := connectedComponentIn_subset _ _ hw
    have hwAc : w ∈ Aᶜ := by
      rw [mem_compl_iff]; intro hwA; exact hwU ⟨w, hwA, rfl⟩
    have hzAc : z ∈ Aᶜ := by
      by_contra hzA
      rw [mem_compl_iff, not_not] at hzA
      have hD : connectedComponentIn ((↑) '' A)ᶜ (z : RiemannSphere) = ∅ :=
        connectedComponentIn_eq_empty (by intro h; exact h ⟨z, hzA, rfl⟩)
      rw [hD] at hw; exact hw
    have hzP : z ∈ P := by rw [hP]; exact mem_connectedComponentIn hzAc
    have haU : (z : RiemannSphere) ∈ ((↑) '' A)ᶜ := by
      rw [mem_compl_iff]; rintro ⟨a, ha, hza⟩
      exact hzAc (OnePoint.coe_injective hza ▸ ha)
    by_cases hPbdd : Bornology.IsBounded P
    · -- `P` bounded: separate with `↑''P` and `↑''(Aᶜ \ P) ∪ {∞}`
      have hAPclosed : IsClosed (A ∪ P) := by
        have hsub : closure P ⊆ A ∪ P := by
          rw [closure_eq_self_union_frontier, ← Set.union_comm P A]
          exact Set.union_subset_union (subset_refl P) hfront
        have heq : A ∪ P = A ∪ closure P :=
          Set.Subset.antisymm (Set.union_subset_union (subset_refl A) subset_closure)
            (Set.union_subset Set.subset_union_left hsub)
        rw [heq]; exact hAcl.union isClosed_closure
      have hAPbdd : Bornology.IsBounded (A ∪ P) := hA.isBounded.union hPbdd
      have hAPc : IsCompact (A ∪ P) :=
        Metric.isCompact_iff_isClosed_bounded.mpr ⟨hAPclosed, hAPbdd⟩
      have hpre : (OnePoint.some ⁻¹' ((↑) '' (Aᶜ \ P) ∪ {∞} : Set RiemannSphere) : Set ℂ) = Aᶜ \ P := by
        change {c : ℂ | (c : RiemannSphere) ∈ ((↑) '' (Aᶜ \ P) ∪ {∞} : Set RiemannSphere)} = Aᶜ \ P
        ext c
        rw [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, Set.mem_singleton_iff]
        constructor
        · rintro (⟨x, hx, hxc⟩ | hinf)
          · rwa [OnePoint.coe_injective hxc] at hx
          · exact absurd hinf (OnePoint.coe_ne_infty c)
        · intro hc; exact Or.inl ⟨c, hc, rfl⟩
      refine notMem_connectedComponentIn_of_separating (α := RiemannSphere)
        (U := ((↑) '' A)ᶜ) (X := (↑) '' P) (X' := (↑) '' (Aᶜ \ P) ∪ {∞})
        (OnePoint.isOpen_image_coe.mpr hPopen) ?_ ?_ ?_ haU ⟨z, hzP, rfl⟩ (Or.inl ⟨w, ⟨hwAc, hwP⟩, rfl⟩) hw
      · refine (OnePoint.isOpen_iff_of_mem' (by simp : (∞ : RiemannSphere) ∈ (↑) '' (Aᶜ \ P) ∪ {∞})).mpr ⟨?_, ?_⟩
        · have hdiff : (Aᶜ \ P)ᶜ = A ∪ P := by
            ext c
            rw [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_union]
            constructor
            · intro h; by_cases hc : c ∈ A
              · exact Or.inl hc
              · exact Or.inr (by by_contra hp; exact h ⟨hc, hp⟩)
            · rintro (hc | hp) ⟨hc', hp'⟩
              · exact hc' hc
              · exact hp' hp
          rw [hpre, hdiff]
          exact hAPc
        · rw [hpre]; exact hQPopen
      · -- covering
        intro a ha
        rw [OnePoint.compl_image_coe] at ha
        rcases ha with ⟨c, hc, hca⟩ | hinf
        · rw [← hca]
          rcases em (c ∈ P) with hcP | hcP
          · exact Or.inl ⟨c, hcP, rfl⟩
          · exact Or.inr (Or.inl ⟨c, ⟨hc, hcP⟩, rfl⟩)
        · rw [Set.mem_singleton_iff] at hinf
          rw [hinf]
          exact Or.inr (Or.inr rfl)
      · -- disjointness
        rw [Set.disjoint_left]
        rintro a ⟨c, hcP, hac⟩ hain
        rcases hain with ⟨e, he, hea⟩ | hin
        · exact he.2 (OnePoint.coe_injective (hac.trans hea.symm) ▸ hcP)
        · rw [Set.mem_singleton_iff] at hin
          exact OnePoint.coe_ne_infty c (hac.trans hin)
    · -- `P` unbounded: separate with `↑''P ∪ {∞}` and `↑''(Aᶜ \ P)`
      have hPunb : ∃ w₀ ∈ P, max C 0 < ‖w₀‖ := by
        by_contra hcon
        simp only [not_exists, not_and, not_lt] at hcon
        exact hPbdd (isBounded_iff_forall_norm_le.mpr ⟨max C 0, hcon⟩)
      have hsubP : ({w : ℂ | max C 0 < ‖w‖}) ⊆ P := by
        obtain ⟨w₀, hw₀P, hw₀R⟩ := hPunb
        have h1 : {w : ℂ | max C 0 < ‖w‖} ⊆ connectedComponentIn Aᶜ w₀ :=
          IsPreconnected.subset_connectedComponentIn (isPreconnected_lt_norm (max C 0) (le_max_right _ _))
            hw₀R hfar
        have h2 : connectedComponentIn Aᶜ w₀ = P :=
          (connectedComponentIn_eq (show w₀ ∈ connectedComponentIn Aᶜ z by rw [← hP]; exact hw₀P)).symm.trans hP.symm
        rw [h2] at h1
        exact h1
      have hPc : IsCompact Pᶜ := by
        refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨hPopen.isClosed_compl, ?_⟩
        refine isBounded_iff_forall_norm_le.mpr ⟨max C 0, fun u hu => ?_⟩
        by_contra hlt
        exact hu (hsubP (not_le.mp hlt))
      have hpre : (OnePoint.some ⁻¹' ((↑) '' P ∪ {∞} : Set RiemannSphere) : Set ℂ) = P := by
        change {c : ℂ | (c : RiemannSphere) ∈ ((↑) '' P ∪ {∞} : Set RiemannSphere)} = P
        ext c
        rw [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, Set.mem_singleton_iff]
        constructor
        · rintro (⟨x, hx, hxc⟩ | hinf)
          · rwa [OnePoint.coe_injective hxc] at hx
          · exact absurd hinf (OnePoint.coe_ne_infty c)
        · intro hc; exact Or.inl ⟨c, hc, rfl⟩
      refine notMem_connectedComponentIn_of_separating (α := RiemannSphere)
        (U := ((↑) '' A)ᶜ) (X := (↑) '' P ∪ {∞}) (X' := (↑) '' (Aᶜ \ P))
        ?_ (OnePoint.isOpen_image_coe.mpr hQPopen) ?_ ?_ haU (Or.inl ⟨z, hzP, rfl⟩) ⟨w, ⟨hwAc, hwP⟩, rfl⟩ hw
      · refine (OnePoint.isOpen_iff_of_mem' (by simp : (∞ : RiemannSphere) ∈ (↑) '' P ∪ {∞})).mpr ⟨?_, ?_⟩
        · rw [hpre]; exact hPc
        · rw [hpre]; exact hPopen
      · -- covering
        intro a ha
        rw [OnePoint.compl_image_coe] at ha
        rcases ha with ⟨c, hc, hca⟩ | hinf
        · rw [← hca]
          rcases em (c ∈ P) with hcP | hcP
          · exact Or.inl (Or.inl ⟨c, hcP, rfl⟩)
          · exact Or.inr ⟨c, ⟨hc, hcP⟩, rfl⟩
        · rw [Set.mem_singleton_iff] at hinf
          rw [hinf]
          exact Or.inl (Or.inr rfl)
      · -- disjointness
        rw [Set.disjoint_left]
        rintro a hain ⟨e, he, hea⟩
        rcases hain with ⟨c, hcP, hac⟩ | hin
        · exact he.2 (OnePoint.coe_injective (hac.trans hea.symm) ▸ hcP)
        · rw [Set.mem_singleton_iff] at hin
          exact OnePoint.coe_ne_infty e (hea.trans hin)
  · -- the easy direction
    intro w hwP
    have hwP' : w ∈ connectedComponentIn Aᶜ z := by rw [← hP]; exact hwP
    have hzAc : z ∈ Aᶜ := connectedComponentIn_nonempty_iff.mp ⟨w, hwP'⟩
    have hzP : z ∈ P := by rw [hP]; exact mem_connectedComponentIn hzAc
    have hsub : ((↑) '' P : Set RiemannSphere) ⊆ ((↑) '' A)ᶜ := by
      rintro _ ⟨c, hc, rfl⟩
      rw [mem_compl_iff]
      rintro ⟨a, ha, hca⟩
      exact (connectedComponentIn_subset Aᶜ z (by rw [← hP]; exact hc)) (OnePoint.coe_injective hca ▸ ha)
    exact IsPreconnected.subset_connectedComponentIn
      (hPpre.image _ OnePoint.continuous_coe.continuousOn)
      ⟨z, hzP, rfl⟩ hsub ⟨w, hwP, rfl⟩

/-- **Comparison of components of the complement of a compact subset of the sphere which misses
`∞`**: the sphere-component of a finite point meets `ℂ` exactly in the plane-component. -/
theorem connectedComponentIn_compl_coe_of_infty_notMem {A : Set RiemannSphere}
    (hAc : IsCompact A) (hAinf : ∞ ∉ A) (z : ℂ) :
    {w : ℂ | (w : RiemannSphere) ∈ connectedComponentIn Aᶜ (z : RiemannSphere)}
      = connectedComponentIn ((OnePoint.some ⁻¹' A)ᶜ : Set ℂ) z := by
  have hAeq : ((↑) '' (OnePoint.some ⁻¹' A) : Set RiemannSphere) = A := by
    apply Set.Subset.antisymm
    · rintro _ ⟨c, hc, rfl⟩; exact hc
    · intro a ha
      obtain ⟨c, hc⟩ := OnePoint.ne_infty_iff_exists.mp (fun h => hAinf (h ▸ ha))
      exact ⟨c, (show OnePoint.some c ∈ A from hc.symm ▸ ha), hc⟩
  have hAcℂ : IsCompact (OnePoint.some ⁻¹' A : Set ℂ) := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · exact hAc.isClosed.preimage OnePoint.continuous_coe
    · have hmem : Aᶜ ∈ 𝓝 (∞ : RiemannSphere) := hAc.isClosed.isOpen_compl.mem_nhds hAinf
      obtain ⟨K, ⟨-, hKcpt⟩, hKsub⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hmem
      have hsub : (OnePoint.some ⁻¹' A : Set ℂ) ⊆ K := by
        intro c hc
        by_contra hcK
        exact hKsub (Or.inl ⟨c, hcK, rfl⟩) hc
      obtain ⟨D, hD⟩ := hKcpt.isBounded.exists_norm_le
      exact isBounded_iff_forall_norm_le.mpr ⟨D, fun c hc => hD c (hsub hc)⟩
  have h1 := connectedComponentIn_compl_coe hAcℂ z
  rw [hAeq] at h1
  exact h1

theorem janiszewskiDisjointSphere {F₁ F₂ : Set Work.Smooth.SphereJordan.RiemannSphere} (h₁ : IsCompact F₁) (h₂ : IsCompact F₂) (hd : Disjoint F₁ F₂) {x y : Work.Smooth.SphereJordan.RiemannSphere} (hx : x ∉ F₁ ∪ F₂) (hy : y ∉ F₁ ∪ F₂) (h₁' : y ∈ connectedComponentIn F₁ᶜ x) (h₂' : y ∈ connectedComponentIn F₂ᶜ x) : y ∈ connectedComponentIn (F₁ ∪ F₂)ᶜ x := by
  classical
  -- a point `p` off `F₁ ∪ F₂ ∪ {x, y}`
  have hKopen : IsOpen ((F₁ ∪ F₂)ᶜ : Set RiemannSphere) := (h₁.union h₂).isClosed.isOpen_compl
  have hxK : x ∈ ((F₁ ∪ F₂)ᶜ : Set RiemannSphere) := hx
  have hInf : (((F₁ ∪ F₂)ᶜ : Set RiemannSphere)).Infinite :=
    Set.Infinite.of_accPt (hKopen.preperfect x hxK)
  obtain ⟨p, hpK, hpne⟩ := hInf.exists_notMem_finset ({x, y} : Finset RiemannSphere)
  have hpF : p ∉ F₁ ∪ F₂ := hpK
  have hpx : p ≠ x := fun h => hpne (by simp [h])
  have hpy : p ≠ y := fun h => hpne (by simp [h])
  obtain ⟨Φ, hΦ⟩ := exists_homeomorph_infty_eq p
  set Ψ : RiemannSphere ≃ₜ RiemannSphere := Φ.symm with hΨ
  have hΨp : Ψ p = ∞ := by rw [hΨ, ← hΦ, Homeomorph.symm_apply_apply]
  set A : Set RiemannSphere := Ψ '' F₁ with hA
  set B : Set RiemannSphere := Ψ '' F₂ with hB
  set u : RiemannSphere := Ψ x with hu
  set v : RiemannSphere := Ψ y with hv
  have hAc : IsCompact A := by rw [hA]; exact h₁.image Ψ.continuous
  have hBc : IsCompact B := by rw [hB]; exact h₂.image Ψ.continuous
  have hdAB : Disjoint A B := by
    rw [hA, hB, Set.disjoint_left]
    rintro a ⟨c, hcF₁, hca⟩ ⟨e, heF₂, hea⟩
    exact (Set.disjoint_left.mp hd) ((Ψ.injective (hea.trans hca.symm)).symm ▸ hcF₁) heF₂
  have hux : u ∉ A ∪ B := by
    rintro (huA | huB)
    · rw [hu, hA] at huA
      obtain ⟨c, hcF₁, hcu⟩ := huA
      exact hx (Or.inl (Ψ.injective hcu ▸ hcF₁))
    · rw [hu, hB] at huB
      obtain ⟨c, hcF₂, hcu⟩ := huB
      exact hx (Or.inr (Ψ.injective hcu ▸ hcF₂))
  have hvy : v ∉ A ∪ B := by
    rintro (hvA | hvB)
    · rw [hv, hA] at hvA
      obtain ⟨c, hcF₁, hcv⟩ := hvA
      exact hy (Or.inl (Ψ.injective hcv ▸ hcF₁))
    · rw [hv, hB] at hvB
      obtain ⟨c, hcF₂, hcv⟩ := hvB
      exact hy (Or.inr (Ψ.injective hcv ▸ hcF₂))
  have hAinf : ∞ ∉ A := by
    rw [hA]; rintro ⟨c, hcF₁, hcA⟩
    exact hpF (Or.inl (Ψ.injective (hcA.trans hΨp.symm) ▸ hcF₁))
  have hBinf : ∞ ∉ B := by
    rw [hB]; rintro ⟨c, hcF₂, hcB⟩
    exact hpF (Or.inr (Ψ.injective (hcB.trans hΨp.symm) ▸ hcF₂))
  have hu_ne : u ≠ ∞ := by
    rw [hu]; intro h
    exact hpx ((Ψ.injective (h.trans hΨp.symm)).symm)
  have hv_ne : v ≠ ∞ := by
    rw [hv]; intro h
    exact hpy ((Ψ.injective (h.trans hΨp.symm)).symm)
  obtain ⟨uc, huc⟩ := OnePoint.ne_infty_iff_exists.mp hu_ne
  obtain ⟨vc, hvc⟩ := OnePoint.ne_infty_iff_exists.mp hv_ne
  -- the hypotheses transported by `Ψ`
  have hA'' : v ∈ connectedComponentIn Aᶜ u := by
    have hφ : Ψ '' connectedComponentIn F₁ᶜ x = connectedComponentIn (Ψ '' F₁ᶜ) (Ψ x) :=
      Ψ.image_connectedComponentIn (by rw [mem_compl_iff]; intro h; exact hx (Or.inl h))
    have himg : Ψ '' F₁ᶜ = (Ψ '' F₁)ᶜ := Set.image_compl_eq Ψ.bijective
    rw [himg, ← hA, ← hu] at hφ
    rw [← hφ]; exact ⟨y, h₁', hv.symm⟩
  have hB'' : v ∈ connectedComponentIn Bᶜ u := by
    have hφ : Ψ '' connectedComponentIn F₂ᶜ x = connectedComponentIn (Ψ '' F₂ᶜ) (Ψ x) :=
      Ψ.image_connectedComponentIn (by rw [mem_compl_iff]; intro h; exact hx (Or.inr h))
    have himg : Ψ '' F₂ᶜ = (Ψ '' F₂)ᶜ := Set.image_compl_eq Ψ.bijective
    rw [himg, ← hB, ← hu] at hφ
    rw [← hφ]; exact ⟨y, h₂', hv.symm⟩
  -- the plane sets
  let Aℂ : Set ℂ := OnePoint.some ⁻¹' A
  let Bℂ : Set ℂ := OnePoint.some ⁻¹' B
  have hAeq : ((↑) '' Aℂ : Set RiemannSphere) = A := by
    apply Set.Subset.antisymm
    · rintro _ ⟨c, hc, rfl⟩; exact hc
    · intro a ha
      obtain ⟨c, hc⟩ := OnePoint.ne_infty_iff_exists.mp (fun h => hAinf (h ▸ ha))
      exact ⟨c, (show OnePoint.some c ∈ A from hc.symm ▸ ha), hc⟩
  have hBeq : ((↑) '' Bℂ : Set RiemannSphere) = B := by
    apply Set.Subset.antisymm
    · rintro _ ⟨c, hc, rfl⟩; exact hc
    · intro a ha
      obtain ⟨c, hc⟩ := OnePoint.ne_infty_iff_exists.mp (fun h => hBinf (h ▸ ha))
      exact ⟨c, (show OnePoint.some c ∈ B from hc.symm ▸ ha), hc⟩
  have hAℂc : IsCompact Aℂ := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · exact hAc.isClosed.preimage OnePoint.continuous_coe
    · have hmem : Aᶜ ∈ 𝓝 (∞ : RiemannSphere) := hAc.isClosed.isOpen_compl.mem_nhds hAinf
      obtain ⟨K, ⟨-, hKcpt⟩, hKsub⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hmem
      have hsub : Aℂ ⊆ K := by
        intro c hc
        by_contra hcK
        exact hKsub (Or.inl ⟨c, hcK, rfl⟩) hc
      obtain ⟨D, hD⟩ := hKcpt.isBounded.exists_norm_le
      exact isBounded_iff_forall_norm_le.mpr ⟨D, fun c hc => hD c (hsub hc)⟩
  have hBℂc : IsCompact Bℂ := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · exact hBc.isClosed.preimage OnePoint.continuous_coe
    · have hmem : Bᶜ ∈ 𝓝 (∞ : RiemannSphere) := hBc.isClosed.isOpen_compl.mem_nhds hBinf
      obtain ⟨K, ⟨-, hKcpt⟩, hKsub⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hmem
      have hsub : Bℂ ⊆ K := by
        intro c hc
        by_contra hcK
        exact hKsub (Or.inl ⟨c, hcK, rfl⟩) hc
      obtain ⟨D, hD⟩ := hKcpt.isBounded.exists_norm_le
      exact isBounded_iff_forall_norm_le.mpr ⟨D, fun c hc => hD c (hsub hc)⟩
  have hdAℂBℂ : Disjoint Aℂ Bℂ := by
    rw [Set.disjoint_left]
    rintro c hcA hcB
    exact Set.disjoint_left.mp hdAB hcA hcB
  have hucAB : uc ∉ Aℂ ∪ Bℂ := by
    rintro (hcA | hcB)
    · exact hux (Or.inl (huc ▸ hcA))
    · exact hux (Or.inr (huc ▸ hcB))
  have hvcAB : vc ∉ Aℂ ∪ Bℂ := by
    rintro (hcA | hcB)
    · exact hvy (Or.inl (hvc ▸ hcA))
    · exact hvy (Or.inr (hvc ▸ hcB))
  -- the plane hypotheses
  have hpl₁ : vc ∈ connectedComponentIn (Aℂᶜ : Set ℂ) uc := by
    have hlhs : (vc : RiemannSphere) ∈ connectedComponentIn Aᶜ (uc : RiemannSphere) := by
      rw [huc, hvc]; exact hA''
    exact (Set.ext_iff.mp (connectedComponentIn_compl_coe_of_infty_notMem hAc hAinf uc) vc).mp hlhs
  have hpl₂ : vc ∈ connectedComponentIn (Bℂᶜ : Set ℂ) uc := by
    have hlhs : (vc : RiemannSphere) ∈ connectedComponentIn Bᶜ (uc : RiemannSphere) := by
      rw [huc, hvc]; exact hB''
    exact (Set.ext_iff.mp (connectedComponentIn_compl_coe_of_infty_notMem hBc hBinf uc) vc).mp hlhs
  have hplane : vc ∈ connectedComponentIn ((Aℂ ∪ Bℂ)ᶜ : Set ℂ) uc :=
    janiszewskiDisjoint hAℂc hBℂc hdAℂBℂ hucAB hvcAB hpl₁ hpl₂
  -- back to the sphere
  have hS : v ∈ connectedComponentIn (A ∪ B)ᶜ u := by
    have hsub : ((↑) '' connectedComponentIn ((Aℂ ∪ Bℂ)ᶜ : Set ℂ) uc : Set RiemannSphere)
        ⊆ (A ∪ B)ᶜ := by
      rintro _ ⟨c, hc, rfl⟩
      rw [mem_compl_iff]
      intro hcAB
      exact (connectedComponentIn_subset _ _ hc) (by
        rcases hcAB with hcA | hcB
        · exact Or.inl hcA
        · exact Or.inr hcB)
    have hsub2 : ((↑) '' connectedComponentIn ((Aℂ ∪ Bℂ)ᶜ : Set ℂ) uc : Set RiemannSphere)
        ⊆ connectedComponentIn (A ∪ B)ᶜ (uc : RiemannSphere) :=
      IsPreconnected.subset_connectedComponentIn
        (isPreconnected_connectedComponentIn.image _ OnePoint.continuous_coe.continuousOn)
        ⟨uc, mem_connectedComponentIn hucAB, rfl⟩ hsub
    have := hsub2 ⟨vc, hplane, hvc⟩
    rwa [huc] at this
  -- back along `Ψ`
  have hcomp : Ψ '' connectedComponentIn (F₁ ∪ F₂)ᶜ x = connectedComponentIn (A ∪ B)ᶜ u := by
    rw [Ψ.image_connectedComponentIn (by rw [mem_compl_iff]; exact hx),
      Set.image_compl_eq Ψ.bijective, Set.image_union, ← hA, ← hB, ← hu]
  obtain ⟨w, hw, hwv⟩ := show v ∈ Ψ '' connectedComponentIn (F₁ ∪ F₂)ᶜ x by rw [hcomp]; exact hS
  exact (Ψ.injective (hwv.trans hv)) ▸ hw

end

end Work.Smooth.SphereJordan
