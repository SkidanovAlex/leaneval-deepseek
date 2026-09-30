import Mathlib
import Submission.Work.BW.HilbSerreDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The inductive step of the multigraded Hilbert–Serre theorem

This file proves the induction in `hilb_serre_poly` by running the standard exact-sequence
argument on the quotient by `X x • ⊤` and the kernel of multiplication by `X x`.  The three
"external" ingredients (the empty case, the induced gradings, and the rank–nullity identity) are
taken as hypotheses so that they can be proved independently.
-/

namespace Work.BW

open MvPolynomial
open scoped Pointwise

universe u

/-- The image of a finite-dimensional submodule under a linear map is finite-dimensional. -/
theorem finiteDimensional_map {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N]
    [Module ℂ N] (f : M →ₗ[ℂ] N) (S : Submodule ℂ M) [FiniteDimensional ℂ ↥S] :
    FiniteDimensional ℂ ↥(S.map f) := by
  let g : ↥S →ₗ[ℂ] ↥(S.map f) :=
    { toFun := fun s => ⟨f s.1, Submodule.mem_map_of_mem s.2⟩
      map_add' := fun a b => by ext; simp
      map_smul' := fun c a => by ext; simp }
  exact FiniteDimensional.of_surjective g (by
    rintro ⟨y, hy⟩
    rw [Submodule.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩)

/-- `T` comapped along the subtype of `K` is finite-dimensional when `T` is. -/
theorem finiteDimensional_comap_subtype {N : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (MR N) M] [IsScalarTower ℂ (MR N) M]
    (K : Submodule (MR N) M) (T : Submodule ℂ M) [FiniteDimensional ℂ ↥T] :
    FiniteDimensional ℂ ↥(T.comap (K.subtype : K →ₗ[ℂ] M)) := by
  let g : ↥(T.comap (K.subtype : K →ₗ[ℂ] M)) →ₗ[ℂ] ↥T :=
    { toFun := fun k => ⟨(k.1 : M), by
        have h := Submodule.mem_comap.mp k.2
        simpa using h⟩
      map_add' := fun a b => by ext; rfl
      map_smul' := fun c a => by ext; rfl }
  exact FiniteDimensional.of_injective g (by
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun x : ↥T => (x : M)) h)))

/-- Cardinality of a filtered insert. -/
theorem card_filter_insert {α : Type*} [DecidableEq α] (s : Finset α) (x : α) (hx : x ∉ s)
    (p : α → Prop) [DecidablePred p] :
    ((insert x s).filter p).card = (s.filter p).card + (if p x then 1 else 0) := by
  rw [Finset.filter_insert]
  by_cases hp : p x
  · have hmem : x ∉ s.filter p := by
      rw [Finset.mem_filter]
      rintro ⟨h, -⟩
      exact hx h
    rw [if_pos hp, Finset.card_insert_of_notMem hmem, if_pos hp]
  · rw [if_neg hp, if_neg hp, Nat.add_zero]

theorem hilb_serre_step (N : ℕ)
    (h_empty : ∀ (M : Type u) [AddCommGroup M] [Module ℂ M] [Module (MR N) M]
      [IsScalarTower ℂ (MR N) M] (piece : (Fin (N + 1) →₀ ℤ) → Submodule ℂ M)
      (hg : IsGrading N piece) (hfin : Module.Finite (MR N) M)
      (hfd : ∀ u, Module.Finite ℂ ↥(piece u))
      (h : ∀ v : Fin (N + 1) × Fin 2, ∀ m : M, (MvPolynomial.X v : MR N) • m = 0),
      ∃ P : MvPolynomial (Fin (N + 1)) ℚ,
        ∀ u, (Module.finrank ℂ ↥(piece u) : ℚ) = kFun N (fun _ => 0) P u)
    (h_quot : ∀ (M : Type u) [AddCommGroup M] [Module ℂ M] [Module (MR N) M]
      [IsScalarTower ℂ (MR N) M] (piece : (Fin (N + 1) →₀ ℤ) → Submodule ℂ M)
      (x : Fin (N + 1) × Fin 2), IsGrading N piece →
        IsGrading N (HilbSerre.quoPiece N M piece x))
    (h_ker : ∀ (M : Type u) [AddCommGroup M] [Module ℂ M] [Module (MR N) M]
      [IsScalarTower ℂ (MR N) M] (piece : (Fin (N + 1) →₀ ℤ) → Submodule ℂ M)
      (x : Fin (N + 1) × Fin 2), IsGrading N piece →
        IsGrading N (HilbSerre.kerPiece N M piece x))
    (h_rel : ∀ (M : Type u) [AddCommGroup M] [Module ℂ M] [Module (MR N) M]
      [IsScalarTower ℂ (MR N) M] (piece : (Fin (N + 1) →₀ ℤ) → Submodule ℂ M)
      (x : Fin (N + 1) × Fin 2), IsGrading N piece → (∀ u, Module.Finite ℂ ↥(piece u)) →
        ∀ u, (Module.finrank ℂ ↥(piece u) : ℚ) - (Module.finrank ℂ ↥(piece (u - wZ N x)) : ℚ)
          = (Module.finrank ℂ ↥(HilbSerre.quoPiece N M piece x u) : ℚ)
            - (Module.finrank ℂ ↥(HilbSerre.kerPiece N M piece x u) : ℚ))
    : ∀ (V : Finset (Fin (N + 1) × Fin 2)) (M : Type u) [AddCommGroup M] [Module ℂ M]
      [Module (MR N) M] [IsScalarTower ℂ (MR N) M]
      (piece : (Fin (N + 1) →₀ ℤ) → Submodule ℂ M) (hg : IsGrading N piece)
      (hfin : Module.Finite (MR N) M) (hfd : ∀ u, Module.Finite ℂ ↥(piece u))
      (hV : ∀ v ∉ V, ∀ m : M, (MvPolynomial.X v : MR N) • m = 0),
      ∃ P : MvPolynomial (Fin (N + 1)) ℚ,
        ∀ u, (Module.finrank ℂ ↥(piece u) : ℚ) =
          kFun N (fun i => (V.filter (fun v => v.1 = i)).card) P u := by
  intro V
  induction V using Finset.induction with
  | empty =>
    intro M _ _ _ _ piece hg hfin hfd hV
    obtain ⟨P, hP⟩ := h_empty M piece hg hfin hfd (fun v m => hV v (Finset.notMem_empty v) m)
    refine ⟨P, fun u => ?_⟩
    have h0 : (fun i : Fin (N + 1) => ((∅ : Finset (Fin (N + 1) × Fin 2)).filter
        (fun v => v.1 = i)).card) = fun _ => 0 := by
      funext i; simp
    rw [h0, hP u]
  | insert x s hx ih =>
    intro M _ _ _ _ piece hg hfin hfd hV
    have hgC : IsGrading N (HilbSerre.quoPiece N M piece x) := h_quot M piece x hg
    have hgK : IsGrading N (HilbSerre.kerPiece N M piece x) := h_ker M piece x hg
    have hfinC : Module.Finite (MR N) (M ⧸ HilbSerre.Xsub N M x) := inferInstance
    have hfinK : Module.Finite (MR N) (LinearMap.ker (HilbSerre.mulX N M x)) := inferInstance
    have hfdC : ∀ u, Module.Finite ℂ ↥(HilbSerre.quoPiece N M piece x u) := by
      intro u
      haveI := hfd u
      exact finiteDimensional_map
        (Submodule.mkQ (HilbSerre.Xsub N M x) : M →ₗ[ℂ] (M ⧸ HilbSerre.Xsub N M x)) (piece u)
    have hfdK : ∀ u, Module.Finite ℂ ↥(HilbSerre.kerPiece N M piece x u) := by
      intro u
      haveI := hfd (u - wZ N x)
      exact finiteDimensional_comap_subtype (LinearMap.ker (HilbSerre.mulX N M x))
        (piece (u - wZ N x))
    have hmk : ∀ (r : MR N) (m : M),
        r • (Submodule.mkQ (HilbSerre.Xsub N M x) m)
          = Submodule.mkQ (HilbSerre.Xsub N M x) (r • m) :=
      fun r m => (Submodule.Quotient.mk_smul (HilbSerre.Xsub N M x) r m).symm
    have hVC : ∀ v ∉ s, ∀ c : M ⧸ HilbSerre.Xsub N M x, (MvPolynomial.X v : MR N) • c = 0 := by
      intro v hv c
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (HilbSerre.Xsub N M x) c
      by_cases hvx : v = x
      · rw [hvx, hmk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_pointwise_smul m ((MvPolynomial.X x : MR N)) ⊤ Submodule.mem_top
      · have hnot : v ∉ insert x s := by
          simp only [Finset.mem_insert, not_or]
          exact ⟨hvx, hv⟩
        rw [hmk, hV v hnot m]
        simp
    have hVK : ∀ v ∉ s, ∀ k : LinearMap.ker (HilbSerre.mulX N M x),
        (MvPolynomial.X v : MR N) • k = 0 := by
      intro v hv k
      by_cases hvx : v = x
      · rw [hvx]
        refine Subtype.ext ?_
        show (MvPolynomial.X x : MR N) • (k : M) = (0 : M)
        simpa [HilbSerre.mulX] using LinearMap.mem_ker.mp k.2
      · have hnot : v ∉ insert x s := by
          simp only [Finset.mem_insert, not_or]
          exact ⟨hvx, hv⟩
        refine Subtype.ext ?_
        show (MvPolynomial.X v : MR N) • (k : M) = (0 : M)
        exact hV v hnot (k : M)
    obtain ⟨PC, hPC⟩ := ih (M ⧸ HilbSerre.Xsub N M x) (HilbSerre.quoPiece N M piece x)
      hgC hfinC hfdC hVC
    obtain ⟨PK, hPK⟩ := ih (LinearMap.ker (HilbSerre.mulX N M x)) (HilbSerre.kerPiece N M piece x)
      hgK hfinK hfdK hVK
    set γ : Fin (N + 1) → ℕ := fun i => (s.filter (fun v => v.1 = i)).card with hγ
    set β : Fin (N + 1) → ℕ := fun i => ((insert x s).filter (fun v => v.1 = i)).card with hβ
    have hβeq : β = Function.update γ x.1 (γ x.1 + 1) := by
      funext j
      rw [Function.update_apply]
      by_cases hj : j = x.1
      · rw [if_pos hj, hj]
        show ((insert x s).filter (fun v => v.1 = x.1)).card
            = (s.filter (fun v => v.1 = x.1)).card + 1
        rw [card_filter_insert s x hx (fun v => v.1 = x.1), if_pos rfl]
      · rw [if_neg hj]
        show ((insert x s).filter (fun v => v.1 = j)).card
            = (s.filter (fun v => v.1 = j)).card
        rw [card_filter_insert s x hx (fun v => v.1 = j),
          if_neg (fun h : x.1 = j => hj h.symm), Nat.add_zero]
    have hβpos : 1 ≤ β x.1 := by
      show 1 ≤ ((insert x s).filter (fun v => v.1 = x.1)).card
      exact Finset.card_pos.mpr
        ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_insert_self x s, rfl⟩⟩
    have hupd : Function.update β x.1 (β x.1 - 1) = γ := by
      funext j
      rw [Function.update_apply]
      by_cases hj : j = x.1
      · rw [if_pos hj, hj]
        show ((insert x s).filter (fun v => v.1 = x.1)).card - 1
            = (s.filter (fun v => v.1 = x.1)).card
        rw [card_filter_insert s x hx (fun v => v.1 = x.1), if_pos rfl, Nat.add_sub_cancel]
      · rw [if_neg hj]
        show ((insert x s).filter (fun v => v.1 = j)).card
            = (s.filter (fun v => v.1 = j)).card
        rw [card_filter_insert s x hx (fun v => v.1 = j),
          if_neg (fun h : x.1 = j => hj h.symm), Nat.add_zero]
    have hstep : ∀ u, (Module.finrank ℂ ↥(piece u) : ℚ) - kFun N β (PC - PK) u
        = (Module.finrank ℂ ↥(piece (u - wZ N x)) : ℚ) - kFun N β (PC - PK) (u - wZ N x) := by
      intro u
      have hrel := h_rel M piece x hg hfd u
      have hdiff : kFun N β (PC - PK) u - kFun N β (PC - PK) (u - wZ N x)
          = kFun N γ (PC - PK) u := by
        have h := kFun_diff N β (PC - PK) u x.1 hβpos
        rw [hupd] at h
        rw [show wZ N x = Finsupp.single x.1 (1 : ℤ) from rfl, h]
        ring
      have h1 : kFun N γ (PC - PK) u
          = (Module.finrank ℂ ↥(piece u) : ℚ)
            - (Module.finrank ℂ ↥(piece (u - wZ N x)) : ℚ) := by
        have hPCu : kFun N γ PC u = (Module.finrank ℂ ↥(HilbSerre.quoPiece N M piece x u) : ℚ) :=
          (hPC u).symm
        have hPKu : kFun N γ PK u = (Module.finrank ℂ ↥(HilbSerre.kerPiece N M piece x u) : ℚ) :=
          (hPK u).symm
        rw [kFun_sub, hPCu, hPKu]
        exact hrel.symm
      linarith [hdiff, h1]
    have hiter : ∀ (u : Fin (N + 1) →₀ ℤ) (n : ℕ),
        (Module.finrank ℂ ↥(piece u) : ℚ) - kFun N β (PC - PK) u
          = (Module.finrank ℂ ↥(piece (u - Finsupp.single x.1 ((n : ℤ)))) : ℚ)
            - kFun N β (PC - PK) (u - Finsupp.single x.1 ((n : ℤ))) := by
      intro u n
      induction n with
      | zero => rw [Nat.cast_zero, Finsupp.single_zero, sub_zero]
      | succ n ih =>
        rw [ih, hstep (u - Finsupp.single x.1 ((n : ℤ)))]
        have h1 : (u - Finsupp.single x.1 ((n : ℤ))) - wZ N x
            = u - Finsupp.single x.1 ((n : ℤ) + 1) := by
          rw [show wZ N x = Finsupp.single x.1 (1 : ℤ) from rfl, Finsupp.single_add]
          abel
        have h2 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
        rw [h1, h2]
    refine ⟨PC - PK, fun u => ?_⟩
    have hF0 : (Module.finrank ℂ ↥(piece u) : ℚ) - kFun N β (PC - PK) u = 0 := by
      have h := hiter u ((u x.1).toNat + 1)
      rw [h]
      have hlt : u x.1 < (((u x.1).toNat + 1 : ℕ) : ℤ) := by
        have h' : u x.1 < ((u x.1).toNat : ℤ) + 1 := by
          by_cases hc : 0 ≤ u x.1
          · rw [Int.toNat_of_nonneg hc]; linarith
          · have hz : (u x.1).toNat = 0 := Int.toNat_of_nonpos (le_of_not_ge hc)
            rw [hz]; omega
        push_cast
        linarith
      have hneg : (u - Finsupp.single x.1 ((((u x.1).toNat + 1 : ℕ) : ℤ))) x.1 < 0 := by
        rw [Finsupp.sub_apply, Finsupp.single_eq_same]
        linarith
      rw [hg.eq_bot_of_neg _ ⟨x.1, hneg⟩,
        kFun_eq_zero_of_neg N β (PC - PK) _ x.1 hneg]
      simp
    linarith

end Work.BW
