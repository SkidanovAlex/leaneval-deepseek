import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Solvable
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Nat.Prime.Defs
import Submission.Abelian
import Submission.EmbeddingProblem
import Submission.Work.GroupTheory.isElementaryAbelian_of_minimal_normal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Submission

universe u

open scoped Classical

/-- The trivial group is realizable over `ℚ`: take `ℚ` itself. -/
theorem realizableOver_of_subsingleton (G : Type*) [Group G] [Subsingleton G] :
    RealizableOver ℚ G :=
  (realizableOver_units_zmod 1).of_surjective (1 : (ZMod 1)ˣ →* G)
    (fun g ↦ ⟨1, Subsingleton.elim _ _⟩)

/-- If `A` is a nontrivial normal subgroup of a finite group `G`, the quotient is strictly
smaller. -/
theorem card_quotient_lt {G : Type*} [Group G] [Finite G] {A : Subgroup G} [A.Normal]
    (hA : A ≠ ⊥) : Nat.card (G ⧸ A) < Nat.card G := by
  have h1 : 1 < Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).mpr hA
  have h2 : 0 < A.index := Nat.pos_of_ne_zero A.index_ne_zero_of_finite
  rw [← Subgroup.index_eq_card, ← Subgroup.index_mul_card]
  exact lt_mul_of_one_lt_right h2 h1

/-- Every nontrivial finite group has a nontrivial normal subgroup that is minimal with this
property (with respect to inclusion). -/
theorem exists_minimal_normal (G : Type*) [Group G] [Finite G] (hsub : ¬ Subsingleton G) :
    ∃ A : Subgroup G, A.Normal ∧ A ≠ ⊥ ∧
      ∀ B : Subgroup G, B.Normal → B ≤ A → B ≠ ⊥ → B = A := by
  classical
  haveI : Nontrivial G := not_subsingleton_iff_nontrivial.mp hsub
  have htop : (⊤ : Subgroup G) ≠ ⊥ := top_ne_bot
  have hex : ∃ n : ℕ, ∃ A : Subgroup G, A.Normal ∧ A ≠ ⊥ ∧ Nat.card A = n :=
    ⟨Nat.card (⊤ : Subgroup G), ⊤, inferInstance, htop, rfl⟩
  obtain ⟨A, hAn, hAne, hAcard⟩ := Nat.find_spec hex
  refine ⟨A, hAn, hAne, ?_⟩
  intro B hBn hBA hBne
  have hcardB : Nat.find hex ≤ Nat.card B := Nat.find_min' hex ⟨B, hBn, hBne, rfl⟩
  have hcardA : Nat.card A ≤ Nat.card B := by rw [hAcard]; exact hcardB
  exact Subgroup.eq_of_le_of_card_ge hBA hcardA

/-! ## The embedding step (deep input) -/

/-- **The induction step of Shafarevich's theorem, in its weakest form**: if `A ◁ G` is a
nontrivial *minimal normal* subgroup of a finite solvable group `G` and `G ⧸ A` is realizable
over `ℚ`, then `G` is realizable over `ℚ`.

This is the only unproved statement in the development; `realizable_of_solvable_of` below shows
that it suffices for the target theorem, and `elementaryAbelianKernelStep_implies_minimalNormal`
shows that it is a special case of the classical form
`ElementaryAbelianKernelStep`, because a nontrivial minimal normal subgroup of a finite solvable
group is elementary abelian.  The classical proof (Shafarevich 1954; corrected for `p = 2` in the
Collected Papers and by Schmidt–Wingberg, arXiv:math/9809211) reduces this to *split* embedding
problems with nilpotent (`p`-group) kernels: one constructs *Scholz solutions*, uses the
local–global principle for embedding problems (Hasse's theorem on the Brauer group plus local
class field theory at every prime), and Shafarevich's *shrinking procedure*
(Chevalley–Warning, see `Submission/Work/Shrinking/`) to remove the obstruction. -/
def MinimalNormalKernelStep : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [Group.IsSolvable G] (A : Subgroup G) [A.Normal]
    (_ : A ≠ ⊥), (∀ B : Subgroup G, B.Normal → B ≤ A → B ≠ ⊥ → B = A) →
    RealizableOver ℚ (G ⧸ A) → RealizableOver ℚ G

/-- **Shafarevich's embedding step for elementary abelian kernels**, the classical form.  Let `G`
be a finite solvable group, `A ◁ G` a nontrivial normal subgroup which is elementary abelian of
exponent a prime `p`, and suppose `G ⧸ A` is realizable over `ℚ`.  Then `G` is realizable
over `ℚ`. -/
def ElementaryAbelianKernelStep : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [Group.IsSolvable G] (A : Subgroup G) [A.Normal]
    (_ : A ≠ ⊥) (p : ℕ) (_ : Nat.Prime p) (_ : IsMulCommutative A)
    (_ : ∀ x : A, x ^ p = 1), RealizableOver ℚ (G ⧸ A) → RealizableOver ℚ G

/-- **The deep input**: the only unproved statement of the development. -/
theorem minimalNormalKernelStep : MinimalNormalKernelStep.{u} := by
  sorry

/-- The classical elementary-abelian form implies the minimal form: a nontrivial minimal normal
subgroup of a finite solvable group is elementary abelian. -/
theorem elementaryAbelianKernelStep_implies_minimalNormal (h : ElementaryAbelianKernelStep.{u}) :
    MinimalNormalKernelStep.{u} := by
  intro G _ _ _ A _ hAne hmin hquot
  obtain ⟨p, hp, hcomm, hpow⟩ :=
    Work.GroupTheory.isElementaryAbelian_of_minimal_normal G A hAne hmin
  exact h G A hAne p hp hcomm hpow hquot

/-- The embedding step with the minimal-normal hypothesis, *taken as a hypothesis*. -/
theorem realizable_of_minimal_normal_of (h : MinimalNormalKernelStep.{u})
    (G : Type u) [Group G] [Finite G] [Group.IsSolvable G]
    (A : Subgroup G) [A.Normal] (hAne : A ≠ ⊥)
    (hmin : ∀ B : Subgroup G, B.Normal → B ≤ A → B ≠ ⊥ → B = A)
    (hquot : RealizableOver ℚ (G ⧸ A)) : RealizableOver ℚ G :=
  h G A hAne hmin hquot

/-- **Shafarevich's theorem on solvable Galois groups**, from the embedding step taken as a
hypothesis.  Strong induction on `|G|`. -/
theorem realizable_of_solvable_of (h : MinimalNormalKernelStep.{u}) :
    ∀ (G : Type u) [Group G] [Finite G] [Group.IsSolvable G], RealizableOver ℚ G := by
  classical
  have main : ∀ n : ℕ, ∀ (H : Type u) [Group H] [Finite H] [Group.IsSolvable H],
      Nat.card H = n → RealizableOver ℚ H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H _ _ _ hcard
      by_cases hsub : Subsingleton H
      · exact realizableOver_of_subsingleton H
      · obtain ⟨A, hAn, hAne, hAmin⟩ := exists_minimal_normal H hsub
        haveI := hAn
        have hlt : Nat.card (H ⧸ A) < n := by
          rw [← hcard]
          exact card_quotient_lt hAne
        exact realizable_of_minimal_normal_of h H A hAne hAmin (ih _ hlt (H ⧸ A) rfl)
  exact fun G _ _ _ => main (Nat.card G) G rfl

/-- The embedding step for minimal normal kernels. -/
theorem realizable_of_minimal_normal (G : Type u) [Group G] [Finite G] [Group.IsSolvable G]
    (A : Subgroup G) [A.Normal] (hAne : A ≠ ⊥)
    (hmin : ∀ B : Subgroup G, B.Normal → B ≤ A → B ≠ ⊥ → B = A)
    (hquot : RealizableOver ℚ (G ⧸ A)) : RealizableOver ℚ G :=
  realizable_of_minimal_normal_of minimalNormalKernelStep.{u} G A hAne hmin hquot

/-- **Shafarevich's theorem on solvable Galois groups.** Every finite solvable group is
realizable as a Galois group over `ℚ`. -/
theorem realizable_of_solvable (G : Type u) [Group G] [Finite G] [Group.IsSolvable G] :
    RealizableOver ℚ G :=
  realizable_of_solvable_of minimalNormalKernelStep.{u} G

/-- The classical embedding step with elementary abelian kernel, *proved* from the target theorem
(so it introduces no additional gap). -/
theorem realizable_of_elementary_abelian_kernel (G : Type u) [Group G] [Finite G]
    [Group.IsSolvable G] (A : Subgroup G) [A.Normal] (hAne : A ≠ ⊥)
    (p : ℕ) (hp : Nat.Prime p) (hcomm : IsMulCommutative A) (hpow : ∀ x : A, x ^ p = 1)
    (hquot : RealizableOver ℚ (G ⧸ A)) : RealizableOver ℚ G :=
  realizable_of_solvable G

/-- The classical form `ElementaryAbelianKernelStep`, as a proved statement. -/
theorem elementaryAbelianKernelStep : ElementaryAbelianKernelStep.{u} :=
  fun G _ _ _ A _ hAne p hp hcomm hpow hquot =>
    realizable_of_elementary_abelian_kernel G A hAne p hp hcomm hpow hquot

/-- **The embedding step is exactly as strong as the theorem.**  Every finite solvable group is
realizable over `ℚ` if and only if Shafarevich's embedding step with elementary abelian kernel
holds.  Both directions are proved here, the non-trivial one via the minimal-normal form. -/
theorem realizable_of_solvable_iff :
    (∀ (G : Type u) [Group G] [Finite G] [Group.IsSolvable G], RealizableOver ℚ G) ↔
      ElementaryAbelianKernelStep.{u} :=
  ⟨fun h G _ _ _ A _ _ _ _ _ _ _ => h G,
   fun h => realizable_of_solvable_of (elementaryAbelianKernelStep_implies_minimalNormal h)⟩

end Submission
