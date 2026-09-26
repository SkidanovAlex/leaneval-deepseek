import Mathlib
import Submission.Work.PinchLemma3.ClosedDiscA.exists_ne_zero_inf_span_le_of_intersection_pair
import Submission.Work.PinchLemma3.ClosedDiscA.windingSpan_union_le_sup_of_grounded_inter
import Submission.Work.PinchLemma3.ClosedDiscA.windingSpan_union_le_sup_of_grounded_inter_only
import Submission.Work.PinchLemma3.ClosedDiscA.windingOf_eq_zero_of_not_subset_components
import Submission.Work.PinchLemma3.ClosedDiscA.two_component_intersection
import Submission.Work.PinchLemma3.ClosedDiscA.potential_helpers
import Submission.Work.PinchLemma3.ClosedDiscA.isPathConnected_connectedComponentIn_carrier
import Submission.Work.PinchLemma3.ClosedDiscA.isOpenInCarrier_connectedComponentIn

-- the three hypotheses `hK₁op`, `hK₂op`, `hdisj` of the statement are part of the requested
-- interface but are not needed by the argument below.
set_option linter.unusedVariables false

/-!
# A line outside the winding span of the union of two inessential regions

`Work.PinchLemma3.ClosedDiscA.exists_ne_zero_inf_span_le_of_intersection_pair_general`:
let `A`, `B` be regions of the torus `F = P.carrier` which are open in the carrier and have
vanishing winding span, and suppose that their intersection is the disjoint union of two path
connected pieces `K₁`, `K₂` (`A ∩ B = K₁ ∪ K₂`, `Disjoint K₁ K₂`); no connectivity of `A` or of `B`
themselves is assumed.  Then there is `v ≠ 0` in `ℚ²` whose line meets the winding span of `A ∪ B`
only inside the (vanishing) span of `A` and of `B`; equivalently `WindingSpan P (A ∪ B) ≠ ⊤`.

The sibling `exists_ne_zero_inf_span_le_of_intersection_pair` proves this under the additional
hypothesis that `A` and `B` are path connected.  Two facts make the extra generality work, and they
split the proof into three cases, according to whether the two gates `K₁`, `K₂` can be joined in `A`
and in `B`:

* if the gates are *not* joined inside `A`, then two points of `A ∩ B` which are joined in `A` are
  joined *inside* `A ∩ B` (`joinedIn_inter_of_not_joinedIn`): either they both lie in `K₁` or both in
  `K₂`, where the connectivity of `K₁` resp. `K₂` applies, or they lie in different `K_i`, which is
  excluded.  The `grounded` two-piece criterion
  `windingSpan_union_le_sup_of_grounded_inter_only` (the sibling
  `windingSpan_union_le_sup_of_grounded_inter` without its unused path-connectedness hypothesis)
  then gives `WindingSpan P (A ∪ B) ≤ ⊥`.  The same applies with the roles of `A` and `B` swapped.
* if the gates *are* joined both in `A` and in `B`, then `K₁ ∪ K₂` lies in the connected components
  `α = connectedComponentIn A a₀` and `β = connectedComponentIn B b₀`, which are open in the carrier
  and path connected, and `α ∩ β = K₁ ∪ K₂`.  Every closed curve of `A ∪ B` either ranges in
  `α ∪ β`, in which case the two-component functional criterion
  `winding_psi_eq_zero_of_two_component_inter` kills its winding under the functional vanishing on
  the test loop, or its image leaves `α ∪ β`, in which case that image lies in a *single* component
  of `A` or of `B` (`windingOf_eq_zero_of_not_subset_components`), whence its winding vanishes
  already because `WindingSpan P A = WindingSpan P B = ⊥`.  Either way every winding vector of
  `A ∪ B` is killed, so the winding span of `A ∪ B` is contained in the kernel of a non-zero
  functional, hence `≠ ⊤`.

The final step is the linear algebra `exists_ne_zero_inf_span_le_of_ne_top`.
-/

namespace Work.PinchLemma3.ClosedDiscA

open LeanEval.KnotTheory.PardonDistortion Set

open scoped unitInterval

/-- **The grounding of `A ∩ B` when the two pieces cannot be joined inside `A`.**  If
`A ∩ B = K₁ ∪ K₂` with `K₁`, `K₂` path connected and disjoint, and if a point of `K₁` cannot be
joined to a point of `K₂` by a path in `A` (witnessed by `¬ JoinedIn A a₀ b₀` for `a₀ ∈ K₁`,
`b₀ ∈ K₂`), then any two points of `A ∩ B` which are joined in `A` are already joined in `A ∩ B`:
they must lie in the same one of the two pieces. -/
theorem joinedIn_inter_of_not_joinedIn {A B K₁ K₂ : Set R3} {a₀ b₀ : R3}
    (hinter : A ∩ B = K₁ ∪ K₂)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂)
    (ha₀ : a₀ ∈ K₁) (hb₀ : b₀ ∈ K₂) (hno : ¬ JoinedIn A a₀ b₀) :
    ∀ x ∈ A ∩ B, ∀ y ∈ A ∩ B, JoinedIn A x y → JoinedIn (A ∩ B) x y := by
  intro x hx y hy hxy
  have hx' : x ∈ K₁ ∪ K₂ := hinter ▸ hx
  have hy' : y ∈ K₁ ∪ K₂ := hinter ▸ hy
  have hK₁A : K₁ ⊆ A := fun z hz => (hinter.symm ▸ Set.mem_union_left K₂ hz).1
  have hK₂A : K₂ ⊆ A := fun z hz => (hinter.symm ▸ Set.mem_union_right K₁ hz).1
  have hK₁B : K₁ ⊆ B := fun z hz => (hinter.symm ▸ Set.mem_union_left K₂ hz).2
  have hK₂B : K₂ ⊆ B := fun z hz => (hinter.symm ▸ Set.mem_union_right K₁ hz).2
  rcases hx' with hx₁ | hx₂
  · rcases hy' with hy₁ | hy₂
    · -- both points in `K₁`
      exact (hK₁pc.joinedIn x hx₁ y hy₁).mono (fun z hz => ⟨hK₁A hz, hK₁B hz⟩)
    · -- `x ∈ K₁`, `y ∈ K₂`: excluded by the hypothesis
      exfalso
      exact hno (((hK₁pc.joinedIn a₀ ha₀ x hx₁).mono hK₁A).trans
        (hxy.trans ((hK₂pc.joinedIn y hy₂ b₀ hb₀).mono hK₂A)))
  · rcases hy' with hy₁ | hy₂
    · -- `x ∈ K₂`, `y ∈ K₁`: excluded by the hypothesis
      exfalso
      exact hno (((hK₁pc.joinedIn a₀ ha₀ y hy₁).mono hK₁A).trans
        (hxy.symm.trans ((hK₂pc.joinedIn x hx₂ b₀ hb₀).mono hK₂A)))
    · -- both points in `K₂`
      exact (hK₂pc.joinedIn x hx₂ y hy₂).mono (fun z hz => ⟨hK₂A hz, hK₂B hz⟩)

theorem exists_ne_zero_inf_span_le_of_intersection_pair_general {P : Work.CoreTopology.ParamTorus}
    {A B : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hAc : A ⊆ P.carrier) (hBc : B ⊆ P.carrier)
    (hAop : Work.SurgeryInvariance.IsOpenInCarrier P A)
    (hBop : Work.SurgeryInvariance.IsOpenInCarrier P B)
    (hVA : Work.SurgeryInvariance.WindingSpan P A = ⊥)
    (hVB : Work.SurgeryInvariance.WindingSpan P B = ⊥)
    {K₁ K₂ : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hK₁c : K₁ ⊆ P.carrier) (hK₂c : K₂ ⊆ P.carrier)
    (hK₁op : Work.SurgeryInvariance.IsOpenInCarrier P K₁)
    (hK₂op : Work.SurgeryInvariance.IsOpenInCarrier P K₂)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂)
    (hdisj : Disjoint K₁ K₂) (hinter : A ∩ B = K₁ ∪ K₂) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (A ∪ B) ⊓ Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
        Work.SurgeryInvariance.WindingSpan P A ⊔ Work.SurgeryInvariance.WindingSpan P B := by
  classical
  rw [hVA, hVB, bot_sup_eq]
  -- the two gates
  obtain ⟨a₀, ha₀⟩ := hK₁pc.nonempty
  obtain ⟨b₀, hb₀⟩ := hK₂pc.nonempty
  have hK₁A : K₁ ⊆ A := fun x hx => (hinter.symm ▸ Set.mem_union_left K₂ hx).1
  have hK₁B : K₁ ⊆ B := fun x hx => (hinter.symm ▸ Set.mem_union_left K₂ hx).2
  have hK₂A : K₂ ⊆ A := fun x hx => (hinter.symm ▸ Set.mem_union_right K₁ hx).1
  have hK₂B : K₂ ⊆ B := fun x hx => (hinter.symm ▸ Set.mem_union_right K₁ hx).2
  by_cases hAj : JoinedIn A a₀ b₀
  · by_cases hBj : JoinedIn B a₀ b₀
    · -- ---------------------------------------------------------------- case (iii) --
      -- the gates are joined both in `A` and in `B`: the extra generator
      have hbj : b₀ ∈ connectedComponentIn A a₀ := by
        have hpre : IsPreconnected (Set.range hAj.somePath) :=
          isPreconnected_range (f := (hAj.somePath : unitInterval → R3)) hAj.somePath.continuous
        refine hpre.subset_connectedComponentIn (x := a₀) ⟨0, hAj.somePath.source⟩ ?_
          ⟨1, hAj.somePath.target⟩
        rintro y ⟨t, rfl⟩
        exact hAj.somePath_mem t
      have ha₀β : a₀ ∈ connectedComponentIn B b₀ := by
        have hpre : IsPreconnected (Set.range hBj.somePath) :=
          isPreconnected_range (f := (hBj.somePath : unitInterval → R3)) hBj.somePath.continuous
        refine hpre.subset_connectedComponentIn (x := b₀) ⟨1, hBj.somePath.target⟩ ?_
          ⟨0, hBj.somePath.source⟩
        rintro y ⟨t, rfl⟩
        exact hBj.somePath_mem t
      -- the two components through the gates
      set α : Set R3 := connectedComponentIn A a₀ with hαdef
      set β : Set R3 := connectedComponentIn B b₀ with hβdef
      have hαc : α ⊆ P.carrier := fun y hy => hAc (connectedComponentIn_subset A a₀ hy)
      have hβc : β ⊆ P.carrier := fun y hy => hBc (connectedComponentIn_subset B b₀ hy)
      have hαop : Work.SurgeryInvariance.IsOpenInCarrier P α :=
        isOpenInCarrier_connectedComponentIn hAop hAc a₀
      have hβop : Work.SurgeryInvariance.IsOpenInCarrier P β :=
        isOpenInCarrier_connectedComponentIn hBop hBc b₀
      have hαpc : IsPathConnected α :=
        isPathConnected_connectedComponentIn_carrier hAop hAc (hK₁A ha₀)
      have hβpc : IsPathConnected β :=
        isPathConnected_connectedComponentIn_carrier hBop hBc (hK₂B hb₀)
      have hWα : Work.SurgeryInvariance.WindingSpan P α = ⊥ :=
        le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P
          (connectedComponentIn_subset A a₀)) (le_of_eq hVA))
      have hWβ : Work.SurgeryInvariance.WindingSpan P β = ⊥ :=
        le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P
          (connectedComponentIn_subset B b₀)) (le_of_eq hVB))
      -- both gates lie in both components
      have hK₁α : K₁ ⊆ α :=
        (hK₁pc.isConnected.isPreconnected).subset_connectedComponentIn ha₀ hK₁A
      have hK₂α : K₂ ⊆ α := by
        have h := (hK₂pc.isConnected.isPreconnected).subset_connectedComponentIn hb₀ hK₂A
        rwa [← connectedComponentIn_eq hbj] at h
      have hK₁β : K₁ ⊆ β := by
        have h := (hK₁pc.isConnected.isPreconnected).subset_connectedComponentIn ha₀ hK₁B
        rwa [← connectedComponentIn_eq ha₀β] at h
      have hK₂β : K₂ ⊆ β :=
        (hK₂pc.isConnected.isPreconnected).subset_connectedComponentIn hb₀ hK₂B
      have hinterαβ : α ∩ β = K₁ ∪ K₂ := by
        refine Subset.antisymm ?_ ?_
        · rintro y ⟨hyα, hyβ⟩
          exact hinter ▸ ⟨connectedComponentIn_subset A a₀ hyα,
            connectedComponentIn_subset B b₀ hyβ⟩
        · rintro y (hy | hy)
          · exact ⟨hK₁α hy, hK₁β hy⟩
          · exact ⟨hK₂α hy, hK₂β hy⟩
      -- the gates as points of the carrier, and the test paths
      set a : P.carrier := ⟨a₀, hAc (hK₁A ha₀)⟩ with hadef
      set b : P.carrier := ⟨b₀, hAc (hK₂A hb₀)⟩ with hbdef
      have haK₁ : (a : R3) ∈ K₁ := ha₀
      have hbK₂ : (b : R3) ∈ K₂ := hb₀
      obtain ⟨cA, hcA⟩ := exists_carrierPath (P := P) (X := α) hαc (p := a) (q := b)
        (hαpc.joinedIn a₀ (hK₁α ha₀) b₀ (hK₂α hb₀))
      obtain ⟨cB, hcB⟩ := exists_carrierPath (P := P) (X := β) hβc (p := a) (q := b)
        (hβpc.joinedIn a₀ (hK₁β ha₀) b₀ (hK₂β hb₀))
      -- the winding of the test loop and the integer coefficients of the killing functional
      set w : ℤ × ℤ := Work.SurgeryInvariance.windingOf P
        (closedCurveOfPath (cA.trans cB.symm)) with hwdef
      set Ac : ℤ := if w = 0 then 1 else w.1 with hAcdef
      set Bc : ℤ := if w = 0 then 0 else w.2 with hBcdef
      have hcoef : Bc * w.1 = Ac * w.2 := by
        by_cases hw0 : w = 0
        · rw [hw0]; simp
        · rw [hAcdef, hBcdef, if_neg hw0, if_neg hw0]; ring
      have hne : (Ac, Bc) ≠ 0 := by
        by_cases hw0 : w = 0
        · rw [hAcdef, hBcdef, if_pos hw0, if_pos hw0]; decide
        · rw [hAcdef, hBcdef, if_neg hw0, if_neg hw0]
          intro hcon
          exact hw0 (Prod.ext (by simpa using congrArg Prod.fst hcon)
            (by simpa using congrArg Prod.snd hcon))
      -- the real functional killing the test winding
      set ψR : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
        { toFun := fun p => (Bc : ℝ) * p.1 - (Ac : ℝ) * p.2
          map_add' := by intro p q; simp only [Prod.fst_add, Prod.snd_add]; ring
          map_smul' := by intro c p; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring } with hψRdef
      have hψRZ : ∀ k l : ℤ,
          ψR (((k : ℤ) : ℝ), ((l : ℤ) : ℝ)) = ((Bc * k - Ac * l : ℤ) : ℝ) := by
        intro k l
        rw [hψRdef]
        show (Bc : ℝ) * (k : ℝ) - (Ac : ℝ) * (l : ℝ) = ((Bc * k - Ac * l : ℤ) : ℝ)
        push_cast
        ring
      have hψw : psiDisp ψR (cA.trans cB.symm) = 0 := by
        rw [psiDisp_eq_psi_periodShift ψR (cA.trans cB.symm), ← hwdef]
        rw [show Work.TorusCover.periodShift w
            = (2 * Real.pi) • (((w.1 : ℝ), (w.2 : ℝ)) : ℝ × ℝ) from by
              ext <;> simp [Work.TorusCover.periodShift, smul_eq_mul, mul_comm]]
        rw [map_smul, hψRZ w.1 w.2]
        have : ((Bc * w.1 - Ac * w.2 : ℤ) : ℝ) = 0 := by rw [hcoef]; simp
        rw [this, smul_zero]
      -- the two gates lie in the intersection of the two regions
      have hABα : A ∩ B ⊆ connectedComponentIn A a₀ := by
        intro x hx
        rcases (hinter ▸ hx : x ∈ K₁ ∪ K₂) with h | h
        · exact hK₁α h
        · exact hK₂α h
      have hABβ : A ∩ B ⊆ connectedComponentIn B b₀ := by
        intro x hx
        rcases (hinter ▸ hx : x ∈ K₁ ∪ K₂) with h | h
        · exact hK₁β h
        · exact hK₂β h
      -- every winding vector of `A ∪ B` is killed
      have hkill : ∀ (γ : Work.CoreTopology.ClosedCurve P), (∀ t : ℝ, γ t ∈ A ∪ B) →
          ψR (((Work.SurgeryInvariance.windingOf P γ).1 : ℝ),
               ((Work.SurgeryInvariance.windingOf P γ).2 : ℝ)) = 0 := by
        intro γ hγ
        by_cases hsub : Set.range γ.γ ⊆ α ∪ β
        · exact winding_psi_eq_zero_of_two_component_inter (P := P) (A := α) (B := β)
            hαc hβc hαop hβop hαpc hβpc hWα hWβ hK₁c hK₂c hK₁pc hK₂pc hinterαβ
            haK₁ hbK₂ cA hcA cB hcB ψR hψw γ (fun t => hsub ⟨t, rfl⟩)
        · have hz : Work.SurgeryInvariance.windingOf P γ = 0 :=
            windingOf_eq_zero_of_not_subset_components (P := P) hAc hBc hAop hBop
              (hK₁A ha₀) (hK₂B hb₀) hABα hABβ hVA hVB γ hγ hsub
          have hpair : (((Work.SurgeryInvariance.windingOf P γ).1 : ℝ),
              ((Work.SurgeryInvariance.windingOf P γ).2 : ℝ)) = ((0 : ℝ), (0 : ℝ)) := by
            rw [hz]; simp
          rw [hpair, hψRdef]
          simp
      -- the rational functional with the same coefficients
      set ψQ : (ℚ × ℚ) →ₗ[ℚ] ℚ :=
        { toFun := fun p => (Bc : ℚ) * p.1 - (Ac : ℚ) * p.2
          map_add' := by intro p q; simp only [Prod.fst_add, Prod.snd_add]; ring
          map_smul' := by intro c p; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring } with hψQdef
      have hψQZ : ∀ k l : ℤ,
          ψQ (((k : ℤ) : ℚ), ((l : ℤ) : ℚ)) = ((Bc * k - Ac * l : ℤ) : ℚ) := by
        intro k l
        rw [hψQdef]
        show (Bc : ℚ) * (k : ℚ) - (Ac : ℚ) * (l : ℚ) = ((Bc * k - Ac * l : ℤ) : ℚ)
        push_cast
        ring
      have hker : Work.SurgeryInvariance.WindingSpan P (A ∪ B) ≤ LinearMap.ker ψQ := by
        rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_le]
        rintro v ⟨γ, hγ, rfl⟩
        change ψQ ((((Work.SurgeryInvariance.windingOf P γ).1 : ℤ) : ℚ),
          (((Work.SurgeryInvariance.windingOf P γ).2 : ℤ) : ℚ)) = 0
        have hR := hkill γ hγ
        have hZ : Bc * (Work.SurgeryInvariance.windingOf P γ).1
            - Ac * (Work.SurgeryInvariance.windingOf P γ).2 = 0 := by
          have hcast : (((Bc * (Work.SurgeryInvariance.windingOf P γ).1
              - Ac * (Work.SurgeryInvariance.windingOf P γ).2 : ℤ)) : ℝ) = 0 := by
            rw [← hψRZ (Work.SurgeryInvariance.windingOf P γ).1
              (Work.SurgeryInvariance.windingOf P γ).2]
            exact hR
          exact_mod_cast hcast
        rw [hψQZ, hZ, Int.cast_zero]
      have hψQne : ψQ ≠ 0 := by
        intro h0
        have h1 : ((Bc : ℚ)) = 0 := by
          have hc := congrArg (fun f : (ℚ × ℚ) →ₗ[ℚ] ℚ => f ((1 : ℚ), (0 : ℚ))) h0
          simp only [LinearMap.zero_apply] at hc
          rw [hψQdef] at hc
          simpa using hc
        have h2 : ((Ac : ℚ)) = 0 := by
          have hc := congrArg (fun f : (ℚ × ℚ) →ₗ[ℚ] ℚ => f ((0 : ℚ), (1 : ℚ))) h0
          simp only [LinearMap.zero_apply] at hc
          rw [hψQdef] at hc
          simpa using hc
        apply hne
        have hB : Bc = 0 := by exact_mod_cast h1
        have hA : Ac = 0 := by exact_mod_cast h2
        rw [hA, hB]; rfl
      have hne_top : Work.SurgeryInvariance.WindingSpan P (A ∪ B) ≠ ⊤ := by
        intro htop
        have hkertop : LinearMap.ker ψQ = ⊤ := le_antisymm le_top (htop ▸ hker)
        exact hψQne (LinearMap.ker_eq_top.mp hkertop)
      exact exists_ne_zero_inf_span_le_of_ne_top _ hne_top
    · -- ---------------------------------------------------------------- case (ii) --
      -- the gates are not joined in `B`: ground on the `B` side
      have hground : ∀ x ∈ B ∩ A, ∀ y ∈ B ∩ A, JoinedIn B x y → JoinedIn (B ∩ A) x y := by
        intro x hx y hy hxy
        exact joinedIn_inter_of_not_joinedIn (A := B) (B := A)
          (by rw [Set.inter_comm]; exact hinter) hK₁pc hK₂pc ha₀ hb₀ hBj
          x ⟨hx.1, hx.2⟩ y ⟨hy.1, hy.2⟩ hxy
      have hle := windingSpan_union_le_sup_of_grounded_inter_only (P := P)
        hBc hAc hBop hAop hground hVB hVA
      have hle' : Work.SurgeryInvariance.WindingSpan P (A ∪ B) ≤ ⊥ := by
        simpa [Set.union_comm, hVA, hVB] using hle
      exact ⟨(1, 0), by simp, le_trans inf_le_left hle'⟩
  · -- ---------------------------------------------------------------- case (i) --
    -- the gates are not joined in `A`: ground on the `A` side
    have hground : ∀ x ∈ A ∩ B, ∀ y ∈ A ∩ B, JoinedIn A x y → JoinedIn (A ∩ B) x y :=
      joinedIn_inter_of_not_joinedIn hinter hK₁pc hK₂pc ha₀ hb₀ hAj
    have hle := windingSpan_union_le_sup_of_grounded_inter_only (P := P)
      hAc hBc hAop hBop hground hVA hVB
    have hle' : Work.SurgeryInvariance.WindingSpan P (A ∪ B) ≤ ⊥ := by
      simpa [hVA, hVB] using hle
    exact ⟨(1, 0), by simp, le_trans inf_le_left hle'⟩

end Work.PinchLemma3.ClosedDiscA
