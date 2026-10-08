import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.GlaubermanZJ.ZJ_eq
import Submission.Work.GlaubermanZJ.thompsonJ_eq
import Submission.Work.GlaubermanZJ.ZJ_le
import Submission.Work.PGroup.All
import Submission.Work.HallHigman.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Vocabulary for Glauberman's Theorem 3.2

Glauberman, *A characteristic subgroup of a p-stable group*, Canad. J. Math. **20** (1968)
1101–1135, Theorem 3.2 (p. 1109) states: for `p` an odd prime, `S` a Sylow `p`-subgroup of a
finite group `X` and `B` an abelian normal `p`-subgroup of `X`, if `X` is `p`-stable then
`Z(J(S)) ∩ B` is normal in `X`.

This file fixes the vocabulary used in the formalisation of that theorem and proves the
elementary normalizer facts the argument needs.

* `ZJcore S B = Z(J(S)) ∩ B` is the subgroup whose normality is the conclusion.
* `normalizer_inf_le_normalizer_inf` : `N(A) ∩ N(B) ≤ N(A ∩ B)`.
* `normalizer_le_normalizer_ZJ` : `N(P) ≤ N(Z(J(P)))` (transported from the delivered
  `Work.PGroup.ZJ_characteristic` through the bridge `Work.GlaubermanZJ.ZJ_eq`).
* `le_normalizer_ZJcore` : the Sylow subgroup `S` normalises `ZJcore S B`.
* `isPGroup_pCore`, `pCore_le_sylow` : `O_p(H)` is a `p`-group, hence lies in every Sylow
  `p`-subgroup of the finite group `H`.
-/

set_option autoImplicit false

open scoped Classical Pointwise

namespace Work.GlaubermanZJ

variable {X : Type*} [Group X]

/-- `Z(J(S)) ∩ B`, the subgroup of Glauberman's Theorem 3.2 whose normality is asserted. -/
def ZJcore {p : ℕ} (S : Sylow p X) (B : Subgroup X) : Subgroup X :=
  Submission.Blueprint.ZJ (S : Subgroup X) ⊓ B

/-- Abelianness is inherited by subgroups. -/
theorem isAbelianSubgroup_mono {A B : Subgroup X}
    (hAB : A ≤ B) (hB : Submission.Blueprint.IsAbelianSubgroup B) :
    Submission.Blueprint.IsAbelianSubgroup A :=
  fun x hx y hy => hB x (hAB hx) y (hAB hy)

/-- A maximal-order abelian subgroup of `S` contained in `P ≤ S` is a maximal-order abelian
subgroup of `P`. -/
theorem isMaxAbelianSubgroup_of_le {S P A : Subgroup X} (hA : IsMaxAbelianSubgroup S A)
    (hAP : A ≤ P) (hPS : P ≤ S) : IsMaxAbelianSubgroup P A :=
  ⟨hAP, hA.2.1, fun B hBP hBab => hA.2.2 B (hBP.trans hPS) hBab⟩

/-- `ZJcore S B ≤ Z(J(S))`. -/
theorem ZJcore_le_ZJ {p : ℕ} (S : Sylow p X) (B : Subgroup X) :
    ZJcore S B ≤ Submission.Blueprint.ZJ (S : Subgroup X) := inf_le_left

/-- `ZJcore S B ≤ B`. -/
theorem ZJcore_le_B {p : ℕ} (S : Sylow p X) (B : Subgroup X) : ZJcore S B ≤ B := inf_le_right

/-- The intersection of the normalizers of two subgroups normalizes their intersection. -/
theorem normalizer_inf_le_normalizer_inf (A B : Subgroup X) :
    Subgroup.normalizer (A : Set X) ⊓ Subgroup.normalizer (B : Set X) ≤
      Subgroup.normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  intro g hg
  rw [Subgroup.mem_inf, Subgroup.mem_normalizer_iff] at hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf]
  constructor
  · intro hx; exact ⟨(hg.1 x).mp hx.1, (hg.2 x).mp hx.2⟩
  · rintro ⟨h1, h2⟩; exact ⟨(hg.1 x).mpr h1, (hg.2 x).mpr h2⟩

/-- `N(P) ≤ N(Z(J(P)))`: `Z(J(P))` is characteristic in `P`, via the delivered
`Work.PGroup.ZJ_characteristic` and the bridge `Work.GlaubermanZJ.ZJ_eq`. -/
theorem normalizer_le_normalizer_ZJ (P : Subgroup X) [Finite P] :
    Subgroup.normalizer (P : Set X) ≤
      Subgroup.normalizer (Submission.Blueprint.ZJ P : Set X) := by
  intro g hg
  have hgm : g ∈ Subgroup.normalizer (P : Set X) := hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  rw [ZJ_eq P]
  have h := Work.PGroup.ZJ_characteristic P g hgm
  rw [Work.PGroup.conjBy, Subgroup.pointwise_smul_def] at h
  exact h

/-- The Sylow `p`-subgroup `S` normalizes `Z(J(S)) ∩ B` for any normal `B`. -/
theorem le_normalizer_ZJcore {p : ℕ} (S : Sylow p X) (B : Subgroup X) [B.Normal]
    [Finite (S : Subgroup X)] :
    (S : Subgroup X) ≤ Subgroup.normalizer ((ZJcore S B : Subgroup X) : Set X) := by
  have h1 : (S : Subgroup X) ≤
      Subgroup.normalizer (Submission.Blueprint.ZJ (S : Subgroup X) : Set X) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_ZJ (S : Subgroup X))
  have h2 : (S : Subgroup X) ≤ Subgroup.normalizer (B : Set X) := by
    rw [Subgroup.normalizer_eq_top B]
    exact le_top
  exact (le_inf h1 h2).trans (normalizer_inf_le_normalizer_inf _ B)

/-- `O_p(H)` is a `p`-group for a finite group `H`: it is the supremum of the normal subgroups
of `p`-power order, and a supremum of normal `p`-subgroups is a `p`-subgroup
(`Sylow.sSup_of_normal`). -/
theorem isPGroup_pCore (p : ℕ) (H : Type*) [Group H] [Finite H] :
    IsPGroup p (Work.HallHigman.pCore p H) := by
  have h : Work.HallHigman.pCore p H =
      sSup {N : Subgroup H | N.Normal ∧
        Work.HallHigman.IsPiNat (· = p) (Nat.card N)} := rfl
  rw [h]
  refine Sylow.sSup_of_normal _ ?_ ?_
  · rintro N ⟨hNnorm, hNpi⟩
    have hne : Nat.card N ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
    have hk : Nat.card N = p ^ (Nat.card N).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hne (fun {d} hd hdvd => hNpi d hd hdvd)
    exact IsPGroup.of_card (n := (Nat.card N).primeFactorsList.length) hk
  · rintro N ⟨hNnorm, -⟩
    exact hNnorm

/-- `O_p(H)` lies in every Sylow `p`-subgroup of the finite group `H`. -/
theorem pCore_le_sylow {H : Type*} [Group H] [Finite H] {p : ℕ} (S : Sylow p H) :
    Work.HallHigman.pCore p H ≤ (S : Subgroup H) :=
  IsPGroup.le_sylow_of_normal (isPGroup_pCore p H) S

end Work.GlaubermanZJ
