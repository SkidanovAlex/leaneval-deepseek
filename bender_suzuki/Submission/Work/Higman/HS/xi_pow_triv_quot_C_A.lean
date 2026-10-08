import Mathlib
import Submission.Work.Higman.HS.c4_hs_aux
import Submission.Work.Higman.xi_pow_triv_omega1_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Higman.HS

/-- **`ξ ^ (|Ω₁(P)| - 1)` acts trivially on `C/A`** (Higman's Lemma 6, first step, in the
covering formulation).

Let `P` be a Suzuki 2-group, `A ≤ C` normal subgroups with `A` abelian and `ξ`-invariant,
`[C, A] = A² = Ω₁(P)`, and suppose that the only `ξ`-invariant normal subgroups between `A` and
`C` are `A` and `C` (`hcover`, `A ≠ C`).  Then the power `η := ξ ^ (|Ω₁(P)| - 1)` satisfies
`η x * x⁻¹ ∈ A` for every `x ∈ C`, i.e. `η` induces the identity of `C/A`.

Proof.  Since `ξ` permutes the involutions of `P` transitively, `η` fixes `Ω₁(P) = A²`
pointwise (`xi_pow_triv_omega1_iff`).  Let `δ x := (η x) x⁻¹` for `x ∈ C`, and let `E` be the
normal closure of `A ∪ {δ x : x ∈ C}`.  Then `A ≤ E ≤ C` and `E` is `ξ`-invariant, so `hcover`
gives `E = A` or `E = C`.

* If `E = A` then `δ x ∈ A` for all `x ∈ C`, which is the claim.
* If `E = C`, then `C` centralises `A`:  `A` clearly does, and each `δ x` does by Higman's
  commutator collapse (`commutator_pow_mul_inv_eq_one`: `[η x, η y] = [x, y]^η` for `y ∈ A`,
  and `[x, y] ∈ [C, A] = A² = Ω₁` is fixed by `η`, so `[δ x, y] = 1`); finally `A` being normal,
  conjugates of centralising elements still centralise `A`.  Hence `[C, A] = 1`, contradicting
  `[C, A] = A² ≠ 1` (`A² = Ω₁(P)` has more than one element). -/
theorem xi_pow_triv_quot_C_A {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C : Subgroup P} [hAn : A.Normal]
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P) :
    ∀ x ∈ C, (h.xi ^ (Nat.card ↥(Work.Higman.omega1 P) - 1)) x * x⁻¹ ∈ A := by
  haveI : C.Normal := hCn
  set k : ℕ := Nat.card ↥(Work.Higman.omega1 P) - 1 with hk
  have hηΩ : ∀ w ∈ Work.Higman.omega1 P, (h.xi ^ k) w = w := by
    intro w hw
    rw [hk]
    exact xi_pow_card_sub_one_fixes_omega1 h w hw
  have hCA2 : ⁅A, C⁆ = Work.Higman.powSub A 2 := by
    rw [Subgroup.commutator_comm]; exact hCAd
  have homega_ne : Work.Higman.omega1 P ≠ ⊥ := by
    intro hbot
    have h4 := h.omega1_card_ge_four
    rw [hbot, Subgroup.card_bot] at h4
    omega
  have hA2ne : Work.Higman.powSub A 2 ≠ ⊥ := by rw [htop]; exact homega_ne
  -- `ξ` commutes with `η = ξ ^ k` (both as an automorphism and as its inverse)
  have hηξ : ∀ y : P, h.xi ((h.xi ^ k) y) = (h.xi ^ k) (h.xi y) := by
    intro y
    have h1 : h.xi ((h.xi ^ k) y) = (h.xi ^ (k + 1)) y := by
      rw [← MulAut.mul_apply, ← pow_succ']
    have h2 : (h.xi ^ k) (h.xi y) = (h.xi ^ (k + 1)) y := by
      rw [← MulAut.mul_apply, ← pow_succ]
    rw [h1, h2]
  have hηsymm : ∀ y : P, (h.xi : MulAut P).symm ((h.xi ^ k) y)
      = (h.xi ^ k) ((h.xi : MulAut P).symm y) := by
    intro y
    apply h.xi.injective
    rw [MulEquiv.apply_symm_apply, hηξ, MulEquiv.apply_symm_apply]
  -- the generating set `A ∪ {δ x : x ∈ C}` and the normal closure `E`
  set G : Set P := (A : Set P) ∪ {e : P | ∃ y : P, y ∈ C ∧ e = (h.xi ^ k) y * y⁻¹} with hG
  set E : Subgroup P := Subgroup.normalClosure G with hE
  have hAE : A ≤ E := by
    intro a ha
    rw [hE]
    exact Subgroup.subset_normalClosure (by rw [hG]; exact Or.inl ha)
  have hEC : E ≤ C := by
    rw [hE]
    refine Subgroup.normalClosure_le_normal ?_
    intro g hg
    rw [hG] at hg
    rcases hg with hgA | ⟨y, hy, rfl⟩
    · exact hAC hgA
    · exact C.mul_mem (mem_of_pow_map_eq (φ := h.xi) hCinv k hy) (C.inv_mem hy)
  -- `G` is `ξ`-invariant, hence so is `E`
  have himg : (⇑(MulEquiv.toMonoidHom h.xi)) '' G = G := by
    apply Set.Subset.antisymm
    · rintro z ⟨w, hw, rfl⟩
      rw [hG] at hw ⊢
      rcases hw with hwA | ⟨y, hy, rfl⟩
      · refine Or.inl ?_
        have h1 : h.xi w ∈ Subgroup.map (h.xi : MulAut P).toMonoidHom A :=
          Subgroup.mem_map_of_mem _ hwA
        rwa [hAxi] at h1
      · refine Or.inr ⟨h.xi y, ?_, ?_⟩
        · have h1 : h.xi y ∈ Subgroup.map (h.xi : MulAut P).toMonoidHom C :=
            Subgroup.mem_map_of_mem _ hy
          rwa [hCinv] at h1
        · show h.xi ((h.xi ^ k) y * y⁻¹) = (h.xi ^ k) (h.xi y) * (h.xi y)⁻¹
          rw [map_mul, map_inv, hηξ]
    · rintro z hz
      rw [hG] at hz
      rcases hz with hzA | ⟨y, hy, rfl⟩
      · refine ⟨(h.xi : MulAut P).symm z, ?_, by simp⟩
        rw [hG]
        exact Or.inl (symm_mem_of_map_eq (h.xi : MulAut P) hAxi hzA)
      · refine ⟨(h.xi : MulAut P).symm ((h.xi ^ k) y * y⁻¹), ?_, by simp⟩
        rw [hG]
        refine Or.inr ⟨(h.xi : MulAut P).symm y,
          symm_mem_of_map_eq (h.xi : MulAut P) hCinv hy, ?_⟩
        rw [map_mul, hηsymm, map_inv]
  have hEinv : E.map (h.xi : MulAut P).toMonoidHom = E := by
    have hmc := Subgroup.map_normalClosure G (h.xi : MulAut P).toMonoidHom h.xi.surjective
    rw [hE, hmc, himg]
  have hEnorm : E.Normal := by rw [hE]; exact Subgroup.normalClosure_normal
  -- a conjugate of an element centralising `A` still centralises `A` (as `A` is normal)
  have hconj_cent : ∀ {g : P}, g ∈ Subgroup.centralizer (A : Set P) → ∀ c : P,
      c * g * c⁻¹ ∈ Subgroup.centralizer (A : Set P) := by
    intro g hg c
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro a ha
    have hca : c⁻¹ * a * c ∈ A := by simpa using hAn.conj_mem a ha c⁻¹
    have h1 : (c⁻¹ * a * c) * g = g * (c⁻¹ * a * c) := hg _ hca
    calc a * (c * g * c⁻¹) = c * (c⁻¹ * a * c) * g * c⁻¹ := by group
      _ = c * ((c⁻¹ * a * c) * g) * c⁻¹ := by group
      _ = c * (g * (c⁻¹ * a * c)) * c⁻¹ := by rw [h1]
      _ = (c * g * c⁻¹) * a := by group
  -- every generator of `E` centralises `A`
  have hGcent : ∀ g ∈ G, g ∈ Subgroup.centralizer (A : Set P) := by
    intro g hg
    rw [hG] at hg
    rcases hg with hgA | ⟨y, hy, rfl⟩
    · refine (Subgroup.mem_centralizer_iff).mpr ?_
      intro a ha
      exact (hAab g hgA a ha).symm
    · refine (Subgroup.mem_centralizer_iff).mpr ?_
      intro a ha
      exact (commutatorElement_eq_one_iff_mul_comm.mp
        (commutator_pow_mul_inv_eq_one h hAab hAxi htop hCA2 hηΩ hy ha)).symm
  have hEcent : E ≤ Subgroup.centralizer (A : Set P) := by
    rw [hE]
    show Subgroup.closure (Group.conjugatesOfSet G) ≤ Subgroup.centralizer (A : Set P)
    rw [Subgroup.closure_le]
    intro z hz
    rw [Group.mem_conjugatesOfSet_iff] at hz
    obtain ⟨g, hg, hconj⟩ := hz
    rw [isConj_iff] at hconj
    obtain ⟨c, hc⟩ := hconj
    rw [← hc]
    exact hconj_cent (hGcent g hg) c
  rcases hcover E hEnorm hEinv hAE hEC with hEA | hEC'
  · intro x hx
    have hmem : (h.xi ^ k) x * x⁻¹ ∈ E := by
      rw [hE]
      apply Subgroup.subset_normalClosure
      rw [hG]
      exact Or.inr ⟨x, hx, rfl⟩
    rw [hEA] at hmem
    exact hmem
  · exfalso
    have hCle : C ≤ Subgroup.centralizer (A : Set P) := hEC' ▸ hEcent
    have hbot : ⁅C, A⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hCle
    rw [hCAd] at hbot
    exact hA2ne hbot

end Work.Higman.HS
