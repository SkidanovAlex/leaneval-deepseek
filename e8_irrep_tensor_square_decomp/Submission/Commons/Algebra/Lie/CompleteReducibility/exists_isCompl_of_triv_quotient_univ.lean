import Mathlib
import Submission.Commons.Algebra.Lie.CompleteReducibility.exists_isCompl_of_triv_quotient

namespace Commons.Algebra.Lie.CompleteReducibility

/-!
# Splitting a Lie submodule with trivial quotient, universe-polymorphic version

This is the universe-polymorphic restatement of
`Commons.Algebra.Lie.CompleteReducibility.exists_isCompl_of_triv_quotient`: the module `V` (and the
modules quantified over in the hypothesis `hsimple`) lives in an arbitrary universe `u` rather than
only in `Type 0`.  The proof is identical in content: the same strong induction on `finrank`,
splitting off the irreducible image `W / W₀` of a maximal proper submodule `W₀ ⋖ W` in the quotient
`V / W₀`, and recursing into a complement.
-/

universe u

theorem exists_isCompl_of_triv_quotient_univ {K : Type*} {L : Type*} [Field K] [LieRing L]
    [LieAlgebra K L]
    (hsimple : ∀ (V : Type u) [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
      [Module.Finite K V] (A : LieSubmodule K L V), LieModule.IsIrreducible K L A →
      (∀ (x : L) (v : V), ⁅x, v⁆ ∈ A) → ∃ M : LieSubmodule K L V, IsCompl A M)
    (V : Type u) [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [Module.Finite K V] (W : LieSubmodule K L V)
    (htriv : ∀ (x : L) (v : V), ⁅x, v⁆ ∈ W) : ∃ W' : LieSubmodule K L V, IsCompl W W' := by
  have key : ∀ n : ℕ, ∀ (V' : Type u) [AddCommGroup V'] [Module K V'] [LieRingModule L V']
      [LieModule K L V'] [Module.Finite K V'], Module.finrank K V' = n →
      ∀ (W' : LieSubmodule K L V'), (∀ (x : L) (v : V'), ⁅x, v⁆ ∈ W') →
      ∃ W'' : LieSubmodule K L V', IsCompl W' W'' := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V' _ _ _ _ _ hfr W' htriv'
      by_cases hbot : W' = ⊥
      · exact ⟨⊤, by rw [hbot]; exact isCompl_bot_top⟩
      · obtain ⟨W₀, hcov⟩ := exists_covBy_of_ne_bot W' hbot
        have hW₀lt : W₀ < W' := hcov.lt
        have hW₀le : W₀ ≤ W' := hW₀lt.le
        set q : V' →ₗ⁅K,L⁆ (V' ⧸ W₀) := LieSubmodule.Quotient.mk' W₀ with hq
        set Abar : LieSubmodule K L (V' ⧸ W₀) := W'.map q with hAbar
        haveI hAbarir : LieModule.IsIrreducible K L Abar := by
          rw [hAbar, hq]
          exact isIrreducible_map_mk'_of_covBy hcov
        have htrivAbar : ∀ (x : L) (y : V' ⧸ W₀), ⁅x, y⁆ ∈ Abar := by
          intro x y
          obtain ⟨v, rfl⟩ := LieSubmodule.Quotient.surjective_mk' W₀ y
          rw [← LieModuleHom.map_lie, hAbar]
          exact LieSubmodule.mem_map_of_mem (htriv' x v)
        obtain ⟨B, hB⟩ := hsimple (V' ⧸ W₀) Abar hAbarir htrivAbar
        set Q : LieSubmodule K L V' := B.comap q with hQ
        have hWQ : W' ⊓ Q = W₀ := by
          apply le_antisymm
          · intro v hv
            rw [LieSubmodule.mem_inf] at hv
            obtain ⟨hvW, hvQ⟩ := hv
            have hvB : q v ∈ B := LieSubmodule.mem_comap.mp hvQ
            have hvA : q v ∈ Abar := by
              rw [hAbar]
              exact LieSubmodule.mem_map_of_mem hvW
            have : q v ∈ Abar ⊓ B := (LieSubmodule.mem_inf Abar B (q v)).mpr ⟨hvA, hvB⟩
            rw [hB.inf_eq_bot, LieSubmodule.mem_bot] at this
            exact (LieSubmodule.Quotient.mk_eq_zero W₀).mp this
          · intro v hv
            refine (LieSubmodule.mem_inf W' Q v).mpr ⟨hW₀le hv, ?_⟩
            rw [LieSubmodule.mem_comap]
            have : q v = 0 := (LieSubmodule.Quotient.mk_eq_zero W₀).mpr hv
            rw [this]
            exact B.zero_mem
        have hVQ : W' ⊔ Q = ⊤ := by
          rw [eq_top_iff]
          intro v _
          have hv : q v ∈ Abar ⊔ B := by rw [hB.sup_eq_top]; trivial
          rw [LieSubmodule.mem_sup] at hv
          obtain ⟨a, ha, b, hb, hab⟩ := hv
          have ha' : a ∈ W'.map q := by rwa [hAbar] at ha
          rw [LieSubmodule.mem_map] at ha'
          obtain ⟨w, hw, hwv⟩ := ha'
          rw [LieSubmodule.mem_sup]
          refine ⟨w, hw, v - w, ?_, by abel⟩
          rw [LieSubmodule.mem_comap]
          have hqw : q (v - w) = b := by rw [map_sub, hwv]; rw [← hab]; abel
          rw [hqw]
          exact hb
        have hW₀Q : W₀ ≤ Q := by rw [← hWQ]; exact inf_le_right
        have hAbarne : Abar ≠ ⊥ := by
          intro h
          have hle : W' ≤ W₀ := (LieSubmodule.Quotient.map_mk'_eq_bot_le W₀ W').mp h
          exact (not_le_of_gt hW₀lt) hle
        have hQne : Q ≠ ⊤ := by
          intro hQtop
          have hBtop : B = ⊤ := by
            rw [eq_top_iff]
            intro y _
            obtain ⟨v, rfl⟩ := LieSubmodule.Quotient.surjective_mk' W₀ y
            have hv : v ∈ Q := by rw [hQtop]; trivial
            exact LieSubmodule.mem_comap.mp hv
          have hAbot : Abar = ⊥ := by
            rw [← hB.inf_eq_bot, hBtop, inf_top_eq]
          exact hAbarne hAbot
        have hQne' : (Q : Submodule K V') ≠ ⊤ := by
          intro h
          exact hQne (LieSubmodule.toSubmodule_injective (by rw [h, LieSubmodule.top_toSubmodule]))
        have hQlt : Module.finrank K ↥Q < n := by
          have := Submodule.finrank_lt (K := K) (V := V') hQne'
          rw [hfr] at this
          exact this
        let W₀' : LieSubmodule K L ↥Q := W₀.comap Q.incl
        have htrivQ : ∀ (x : L) (v : ↥Q), ⁅x, v⁆ ∈ W₀' := by
          intro x v
          rw [show W₀' = W₀.comap Q.incl from rfl, LieSubmodule.mem_comap,
            LieModuleHom.map_lie]
          have h1 : ⁅x, (v : V')⁆ ∈ W' := htriv' x (v : V')
          have h2 : ⁅x, (v : V')⁆ ∈ Q := Q.lie_mem v.2
          have h3 : ⁅x, (v : V')⁆ ∈ W' ⊓ Q :=
            (LieSubmodule.mem_inf W' Q ⁅x, (v : V')⁆).mpr ⟨h1, h2⟩
          rw [hWQ] at h3
          exact h3
        obtain ⟨M', hM'⟩ := ih (Module.finrank K ↥Q) hQlt ↥Q rfl W₀' htrivQ
        have hW₀map : W₀'.map Q.incl = W₀ := by
          rw [show W₀' = W₀.comap Q.incl from rfl,
            LieSubmodule.map_comap_incl Q W₀, inf_eq_right.mpr hW₀Q]
        have hW₀M : W₀ ⊓ (M'.map Q.incl) = ⊥ := by
          have h := congrArg (LieSubmodule.map Q.incl) hM'.inf_eq_bot
          rw [LieSubmodule.map_inf (f := Q.incl) Subtype.coe_injective, LieSubmodule.map_bot,
            hW₀map] at h
          exact h
        have hW₀sup : W₀ ⊔ (M'.map Q.incl) = Q := by
          have h := congrArg (LieSubmodule.map Q.incl) hM'.sup_eq_top
          rw [LieSubmodule.map_sup, LieSubmodule.map_incl_top, hW₀map] at h
          exact h
        refine ⟨M'.map Q.incl, ?_⟩
        have hMleQ : M'.map Q.incl ≤ Q := LieSubmodule.map_incl_le
        have hinf : W' ⊓ (M'.map Q.incl) = ⊥ := by
          refine le_antisymm ?_ bot_le
          have h4 : W' ⊓ (M'.map Q.incl) ≤ W₀ ⊓ (M'.map Q.incl) :=
            le_inf (hWQ ▸ inf_le_inf_left W' hMleQ) inf_le_right
          rwa [hW₀M] at h4
        have hsup : W' ⊔ (M'.map Q.incl) = ⊤ := by
          have hWM : W' ⊔ Q = W' ⊔ (M'.map Q.incl) := by
            conv_lhs => rw [← hW₀sup]
            rw [← sup_assoc, sup_eq_left.mpr hW₀le]
          rw [← hWM, hVQ]
        exact isCompl_iff.mpr ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩
  exact key (Module.finrank K V) V rfl W htriv

end Commons.Algebra.Lie.CompleteReducibility
