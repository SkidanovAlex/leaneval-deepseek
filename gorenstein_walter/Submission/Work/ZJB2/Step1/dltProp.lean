import Mathlib
import Submission.Work.ZJB.Step1.Defs

/-!
# ZJB2 / Step1 — leaf **I.1** (`DltProp`): a bad Sylow subgroup is not inside `N_G(J(S))`

The paper's step (I.1) of Theorem 5.1 (Gorenstein–Walter, via Glauberman 1968 §5, p. 1117):

> if `S₁` is a Sylow `p`-subgroup of `G` with `Z(S) ≤ S₁` and `Z(S) ⊄ Z(J(S₁))` (i.e. `S₁` is
> *bad*), then `S₁ ⊄ N_G(J(S))`.

The formal statement is `Work.ZJB.DltProp p G` (see `Submission/Work/ZJB/Step1/Defs.lean`):
`∀ S S₁, ZS S ≤ S₁ → ¬ ZS S ≤ ZJ S₁ → ¬ S₁ ≤ N(thompsonJ S)`.

## Proof (contrapositive)

Assume `S₁ ≤ N_G(J)` with `J = J(S)`.  Since `S ≤ N_G(J)` as well (`J` is characteristic in `S`),
both `S` and `S₁` are Sylow `p`-subgroups of `N_G(J)`, and hence conjugate *inside* `N_G(J)`:
`exists_mem_normalizer_inv_mul_mem` gives `m ∈ N_G(J)` with `m⁻¹ S₁ m ≤ S`, and since
`|S₁| = |S| = p^{ν_p(|G|)}` this is an equality `m⁻¹ S₁ m = S`.  Conjugation covariance of `J`
then gives `J(S) = J(m⁻¹S₁m) = m⁻¹ J(S₁) m`, and as `m` normalizes `J(S)` the right-hand side is
`J(S₁)`:

* `J(S₁) = J(S)`, hence `Z(J(S₁)) = Z(J(S))`;
* F0 (`Z(P) ≤ Z(J(P))`, proved here as `zs_le_zj`) gives `Z(S) ≤ Z(J(S))`.

Thus `Z(S) ≤ Z(J(S₁))`, contradicting badness.
-/

namespace Work.ZJB2.Step1

/-- **F0.** `Z(P) ≤ Z(J(P))`: a maximal-order abelian `A ≤ P` absorbs `Z(P)`
(`Z(P)·A` is abelian of order `≥ |A|`, hence `= A`), so `Z(P) ≤ J(P)`, and `Z(P)`
centralizes `J(P) ≤ P`. -/
theorem zs_le_zj {G : Type*} [Group G] [Finite G] (P : Subgroup G) :
    Work.ZJB.ZS P ≤ Work.GW2.ZJ P := by
  obtain ⟨A, hA⟩ := Subgroup.maxAbelianIn_nonempty P
  have h1 : Work.ZJB.ZS P ≤ A := Subgroup.centralizer_inf_le_of_mem_maxAbelianIn hA
  have h2 : A ≤ Work.GW2.thompsonJ P := Work.GW2.le_thompsonJ_of_mem_maxAbelianIn hA
  refine le_inf (h1.trans h2) ?_
  exact inf_le_left.trans (Subgroup.centralizer_le (fun x hx => Work.GW2.thompsonJ_le P hx))

/-- A Sylow `p`-subgroup lies in the normalizer of its Thompson subgroup
(`J(P)` is characteristic in `P`). -/
theorem sylow_le_normalizer_thompsonJ {G : Type*} [Group G] {p : ℕ} (S : Sylow p G) :
    (S : Subgroup G) ≤ Subgroup.normalizer (Work.GW2.thompsonJ (S : Subgroup G) : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Work.GW2.thompsonJ_map_conj_eq_of_mem_normalizer (P := (S : Subgroup G))
    (Subgroup.le_normalizer hs)

/-- If a Sylow `p`-subgroup `S₁` is contained in `N_G(J(S))`, then `J(S₁) = J(S)` and
consequently `Z(J(S₁)) = Z(J(S))`. -/
theorem ZJ_eq_of_le_normalizer_thompsonJ {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S S₁ : Sylow p G)
    (hS₁N : (S₁ : Subgroup G) ≤
      Subgroup.normalizer (Work.GW2.thompsonJ (S : Subgroup G) : Set G)) :
    Work.GW2.ZJ (S₁ : Subgroup G) = Work.GW2.ZJ (S : Subgroup G) := by
  have hSN : (S : Subgroup G) ≤
      Subgroup.normalizer (Work.GW2.thompsonJ (S : Subgroup G) : Set G) :=
    sylow_le_normalizer_thompsonJ S
  -- `m ∈ N_G(J(S))` with `m⁻¹ S₁ m ≤ S`
  obtain ⟨m, hmN, hm⟩ := Work.ZJB.exists_mem_normalizer_inv_mul_mem (p := p) S hSN hS₁N S₁.isPGroup'
  have hle : (S₁ : Subgroup G).map (MulAut.conj m⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    simpa [MulAut.conj_apply] using hm v hv
  -- `m⁻¹ S₁ m` has the same order as `S`, hence equals `S`
  have hcard : Nat.card ↥((S₁ : Subgroup G).map (MulAut.conj m⁻¹).toMonoidHom)
      = Nat.card ↥(S : Subgroup G) := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj m⁻¹).toMonoidHom)
      (MulAut.conj m⁻¹).injective, S.card_eq_multiplicity, S₁.card_eq_multiplicity]
  have heq : (S₁ : Subgroup G).map (MulAut.conj m⁻¹).toMonoidHom = (S : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  -- `m` fixes `J(S)`
  have hmapJ : (Work.GW2.thompsonJ (S : Subgroup G)).map (MulAut.conj m).toMonoidHom
      = Work.GW2.thompsonJ (S : Subgroup G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hmN
    exact hmN
  have hcomp : (MulAut.conj m).toMonoidHom.comp (MulAut.conj m⁻¹).toMonoidHom = MonoidHom.id G := by
    ext x; simp [MulAut.conj_apply, mul_assoc]
  -- `J(S₁) = J(S)`
  have hJeq : Work.GW2.thompsonJ (S₁ : Subgroup G) = Work.GW2.thompsonJ (S : Subgroup G) := by
    have h1 : (Work.GW2.thompsonJ (S₁ : Subgroup G)).map (MulAut.conj m⁻¹).toMonoidHom
        = Work.GW2.thompsonJ (S : Subgroup G) := by
      rw [← heq, Work.GW2.thompsonJ_map_conj]
    have h2 := congrArg (fun K : Subgroup G => K.map (MulAut.conj m).toMonoidHom) h1
    rw [Subgroup.map_map, hcomp, Subgroup.map_id, hmapJ] at h2
    exact h2
  rw [Work.GW2.ZJ, Work.GW2.ZJ, hJeq]

/-- **I.1.** A bad Sylow subgroup is not contained in `N_G(J(S))`. -/
theorem dltProp {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] : Work.ZJB.DltProp p G := by
  intro S S₁ _hZS hbad hS₁N
  exact hbad ((zs_le_zj (S : Subgroup G)).trans
    (le_of_eq (ZJ_eq_of_le_normalizer_thompsonJ S S₁ hS₁N).symm))

end Work.ZJB2.Step1
