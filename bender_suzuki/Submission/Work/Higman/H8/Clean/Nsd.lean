import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.equivariant_bihom_trivial
import Submission.Work.Higman.higman_lemma2
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.OmegaAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman.H8.Clean

variable {P : Type} [Group P] [Finite P]

/-! ## Reduction of `no_square_derived`

This file records the structural reduction of the target statement (Higman 1963, §5, exclusion
of the `C₄`-shape of the derived subgroup).  Under the hypotheses of `no_square_derived`:

* `A = ⁅⊤,⊤⁆` is the derived subgroup (hence normal), abelian, `ξ`-invariant,
* `Ω₁(P) ≤ A`, `A ^ (4) = 1`, `A ^ (2) = Ω₁(P)`, `|A| = |Ω₁(P)| ^ 2`,
* every square of `P` lies in `A`.

Reductions proved here:

* `nsd_comm_eq_bot_false` : `⁅A, ⊤⁆ ≠ ⊥`, so (by `nsd_comm_eq_bot_or_omega1`)
  `⁅A, ⊤⁆ = Ω₁(P) = A ^ (2)`.
-/

/-- Under the hypotheses of `no_square_derived`, `A` is normal (it is the derived subgroup). -/
theorem nsd_normal {A : Subgroup P} (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) : A.Normal := by
  rw [← hGs]
  exact Subgroup.commutator_normal _ _

/-- `⁅A, ⊤⁆ ≤ A ^ (2)`: every element of `P` acts on `A` trivially modulo `A²`
(Higman 1963, §3, unipotence). -/
theorem nsd_comm_le (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) :
    ⁅A, (⊤ : Subgroup P)⁆ ≤ powSub A 2 := by
  have hAn : A.Normal := nsd_normal hGs
  rw [Subgroup.commutator_comm, Subgroup.commutator_le]
  intro u _ a ha
  exact commutator_mem_powSub_two h ⟨hAn, hAxi, hAab⟩ u a ha

/-- `⁅A, ⊤⁆` is `ξ`-invariant. -/
theorem nsd_comm_invariant (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A) :
    (⁅A, (⊤ : Subgroup P)⁆).map (h.xi : MulAut P).toMonoidHom = ⁅A, (⊤ : Subgroup P)⁆ := by
  rw [Subgroup.map_commutator, hAxi,
    Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective]

/-- `ξ` permutes the involutions of `P`, hence maps `Ω₁(P)` to itself.  (Re-proved here to keep
this file independent of `Submission.Work.Higman.commutator_le_omega1`, which imports it.) -/
theorem nsd_map_xi_omega1 (h : IsSuzuki2Grp P) :
    (omega1 P).map (h.xi : MulAut P).toMonoidHom = omega1 P := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    rw [h.mem_omega1, ← map_pow, h.mem_omega1.mp hy, map_one]
  · intro x hx
    refine ⟨(h.xi : MulAut P).symm x, ?_, by simp⟩
    rw [SetLike.mem_coe, h.mem_omega1, ← map_pow, h.mem_omega1.mp hx, map_one]

/-- A non-identity element of `Ω₁(P)` has order two. -/
theorem nsd_orderOf_eq_two_of_mem_omega1 (h : IsSuzuki2Grp P) {x : P} (hx : x ∈ omega1 P)
    (hx1 : x ≠ 1) : orderOf x = 2 := by
  have hd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (h.mem_omega1.mp hx)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact absurd (orderOf_eq_one_iff.mp h1) hx1
  · exact h2

/-- `Ω₁(P)` is an irreducible `⟨ξ⟩`-module: a `ξ`-invariant subgroup of `Ω₁(P)` is `⊥` or
`Ω₁(P)`.  (Only the transitivity of `ξ` on the involutions is used.)  Re-proved here to keep
this file independent of `commutator_le_omega1`. -/
theorem nsd_omega1_eq_bot_or_top_of_invariant (h : IsSuzuki2Grp P) {S : Subgroup P}
    (hS : S ≤ omega1 P) (hinv : S.map (h.xi : MulAut P).toMonoidHom = S) :
    S = ⊥ ∨ S = omega1 P := by
  rcases eq_or_ne S ⊥ with hbot | hne
  · exact Or.inl hbot
  right
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hxS : (x : P) ∈ S := x.2
  have hx1' : (x : P) ≠ 1 := fun hc => hx1 (Subtype.ext hc)
  have hpres : ∀ k : ℕ, ∀ y : P, y ∈ S → (h.xi ^ k) y ∈ S := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      have hz : (h.xi ^ k) y ∈ S := ih y hy
      have hgoal : (h.xi ^ (k + 1)) y = h.xi.toMonoidHom ((h.xi ^ k) y) := by
        rw [pow_succ', MulAut.mul_apply]; rfl
      rw [hgoal]
      have hmem : h.xi.toMonoidHom ((h.xi ^ k) y) ∈ S.map (h.xi : MulAut P).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hz
      rwa [hinv] at hmem
  apply le_antisymm hS
  intro y hy
  rcases eq_or_ne y 1 with rfl | hy1
  · exact S.one_mem
  · have hx2 : orderOf (x : P) = 2 := nsd_orderOf_eq_two_of_mem_omega1 h (hS hxS) hx1'
    have hy2 : orderOf y = 2 := nsd_orderOf_eq_two_of_mem_omega1 h hy hy1
    obtain ⟨k, hk⟩ := h.trans (x : P) y hx2 hy2
    rw [← hk]
    exact hpres k (x : P) hxS

/-- **Dichotomy.**  `⁅A, ⊤⁆` is either trivial or all of `A² = Ω₁(P)`. -/
theorem nsd_comm_eq_bot_or_omega1 (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (htop : powSub A 2 = omega1 P) :
    ⁅A, (⊤ : Subgroup P)⁆ = ⊥ ∨ ⁅A, (⊤ : Subgroup P)⁆ = omega1 P := by
  have hle : ⁅A, (⊤ : Subgroup P)⁆ ≤ omega1 P := by
    rw [← htop]
    exact nsd_comm_le h hAxi hAab hGs
  exact nsd_omega1_eq_bot_or_top_of_invariant h hle (nsd_comm_invariant h hAxi)

/-- **The case `⁅A, ⊤⁆ = ⊥` is impossible.**  If `A` is central then `P` has class `2` and every
commutator is an involution, so `A = P' ≤ Ω₁(P) ≤ A` gives `A = Ω₁(P)`, whence `A² = 1`,
contradicting `A² = Ω₁(P) ≠ 1`. -/
theorem nsd_comm_eq_bot_false (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : powSub A 2 = omega1 P) :
    ⁅A, (⊤ : Subgroup P)⁆ ≠ ⊥ := by
  intro hbot
  -- `A` is central
  have hcen : ∀ a ∈ A, ∀ u : P, a * u = u * a := by
    intro a ha u
    have h1 : ⁅a, u⁆ = 1 := by
      have hmem : ⁅a, u⁆ ∈ (⊥ : Subgroup P) := by
        rw [← hbot]
        exact Subgroup.commutator_mem_commutator ha (Subgroup.mem_top u)
      exact Subgroup.mem_bot.mp hmem
    rw [commutatorElement_def] at h1
    have h4 : a * u * a⁻¹ = u := by
      have : (a * u * a⁻¹ * u⁻¹) * u = 1 * u := by rw [h1]
      simpa using this
    calc a * u = a * u * a⁻¹ * a := by group
      _ = u * a := by rw [h4]
  -- `P` has class two
  have hZ : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P := by
    rw [hGs]
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro y
    exact (hcen a ha y).symm
  -- every commutator is an involution
  have hsq1 : ∀ x y : P, ⁅x, y⁆ ^ 2 = 1 := by
    intro x y
    rw [commutator_sq_eq hZ x y]
    have hx : x ^ 2 * y = y * x ^ 2 := hcen (x ^ 2) (hsq x) y
    rw [commutatorElement_def, hx]
    group
  have hDle : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ omega1 P := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [h.mem_omega1]
    exact hsq1 x y
  have hAeq : A = omega1 P :=
    le_antisymm (by rw [← hGs]; exact hDle) hNA
  -- every element of `A` is an involution, so `A ^ (2) = 1`
  have hA2bot : powSub A 2 = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rw [mem_powSub_iff hAab] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx2 : x ^ 2 = 1 := h.mem_omega1.mp (hAeq ▸ hx)
    rw [hx2]
  have hone : Nat.card ↥(omega1 P) = 1 := by
    rw [← htop, hA2bot]
    simp
  have hge := h.omega1_card_ge_four
  omega

/-! ## The `C₄` case: elementary structural facts
Assume from now on the hypotheses of `no_square_derived` together with `⁅A, ⊤⁆ = A ^ (2)`
(the `C₄` case).  We record the elementary consequences that any proof of the exclusion must
build on:

* `nsd_sq_eq` : `P ^ (2) = A` (the derived subgroup is generated by the squares),
* `nsd_coset_sq_wd` : `(u a) ^ 2` and `u ^ 2` differ by an element of `A ^ (2)` for `a ∈ A`,
  i.e. the squaring map descends to a map `P / A → A / A ^ (2)`.

-/

/-- In a group, a commutator is a product of squares:
`[x,y] = (x y)² · (y⁻¹ x⁻¹ y)² · (y⁻¹)²`. -/
theorem commutator_eq_sq_mul (x y : P) :
    ⁅x, y⁆ = (x * y) * (x * y) * ((y⁻¹ * x⁻¹ * y) * (y⁻¹ * x⁻¹ * y)) * (y⁻¹ * y⁻¹) := by
  rw [commutatorElement_def]; group

/-- Every commutator lies in the subgroup generated by the squares. -/
theorem commutator_mem_powSub_top (x y : P) : ⁅x, y⁆ ∈ powSub (⊤ : Subgroup P) 2 := by
  have h1 : (x * y) * (x * y) ∈ powSub (⊤ : Subgroup P) 2 := by
    simpa [pow_two] using
      pow_mem_powSub (A := (⊤ : Subgroup P)) (n := 2) (x := x * y) (Subgroup.mem_top (x * y))
  have h2 : (y⁻¹ * x⁻¹ * y) * (y⁻¹ * x⁻¹ * y) ∈ powSub (⊤ : Subgroup P) 2 := by
    simpa [pow_two] using
      pow_mem_powSub (A := (⊤ : Subgroup P)) (n := 2) (x := y⁻¹ * x⁻¹ * y)
        (Subgroup.mem_top _)
  have h3 : y⁻¹ * y⁻¹ ∈ powSub (⊤ : Subgroup P) 2 := by
    simpa [pow_two] using
      pow_mem_powSub (A := (⊤ : Subgroup P)) (n := 2) (x := y⁻¹) (Subgroup.mem_top _)
  rw [commutator_eq_sq_mul]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h3

/-- Under the hypotheses of `no_square_derived`, `P ^ (2) = A`: the derived subgroup is the
subgroup generated by the squares of `P` (because every square lies in `A` and `P / P ^ (2)`
is abelian). -/
theorem nsd_sq_eq (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (hsq : ∀ x : P, x ^ 2 ∈ A) :
    powSub (⊤ : Subgroup P) 2 = A := by
  refine le_antisymm ?_ ?_
  · rw [powSub, Subgroup.closure_le]
    rintro y ⟨x, -, rfl⟩
    exact hsq x
  · rw [← hGs, Subgroup.commutator_le]
    intro x _ y _
    exact commutator_mem_powSub_top x y

/-- In the `C₄` case, the squaring map is well defined modulo `A ^ (2)`: for `a ∈ A` the
elements `(u * a) ^ 2` and `u ^ 2` differ by an element of `A ^ (2)`.  Here `⁅A, ⊤⁆ ≤ A ^ (2)`
is `nsd_comm_le`. -/
theorem nsd_coset_sq_wd (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (hsq : ∀ x : P, x ^ 2 ∈ A)
    (u : P) {a : P} (ha : a ∈ A) :
    (u * a) * (u * a) * (u * u)⁻¹ ∈ powSub A 2 := by
  have hcom : ⁅u⁻¹, a⁆ ∈ powSub A 2 := by
    have hmem : ⁅u⁻¹, a⁆ ∈ ⁅(⊤ : Subgroup P), A⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top u⁻¹) ha
    have hmem' : ⁅u⁻¹, a⁆ ∈ ⁅A, (⊤ : Subgroup P)⁆ := by
      rwa [Subgroup.commutator_comm] at hmem
    exact nsd_comm_le h hAxi hAab hGs hmem'
  have hsqA : a * a ∈ powSub A 2 := by
    simpa [pow_two] using pow_mem_powSub (A := A) (n := 2) ha
  have hXa : ⁅u⁻¹, a⁆ * (a * a) ∈ powSub A 2 := Subgroup.mul_mem _ hcom hsqA
  have hkey : (u * a) * (u * a) = (u * u) * (⁅u⁻¹, a⁆ * (a * a)) := by
    rw [commutatorElement_def]; group
  rw [hkey]
  have hu2A : u * u ∈ A := by simpa [pow_two] using hsq u
  have hXmem : (⁅u⁻¹, a⁆ * (a * a)) ∈ A := powSub_le (by norm_num) hXa
  rw [hAab (u * u) hu2A _ hXmem, mul_assoc, mul_inv_cancel, mul_one]
  exact hXa

/-- In the `C₄` case `P` has an element of order `8`: were `x ^ 4 = 1` for every `x`, then
every square would lie in `Ω₁(P)`, giving `A = P ^ (2) ≤ Ω₁(P)`, hence `A = Ω₁(P) = A ^ (2)`
and `|A| = |A| ^ 2`, contradicting `|A| = |Ω₁(P)| ^ 2` with `|Ω₁(P)| ≥ 4`. -/
theorem nsd_exists_ord_eight (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : powSub A 2 = omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(omega1 P)) ^ 2) :
    ∃ x : P, x ^ 4 ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hle : powSub (⊤ : Subgroup P) 2 ≤ omega1 P := by
    rw [powSub, Subgroup.closure_le]
    rintro y ⟨x, -, rfl⟩
    refine h.mem_omega1.mpr ?_
    have h2 : x ^ 4 = (x ^ 2) ^ 2 := by simpa using (pow_mul x 2 2)
    rw [← h2]
    exact hcon x
  have hA : A = omega1 P := by
    rw [← nsd_sq_eq h hGs hsq]
    exact le_antisymm hle (by rw [← htop]; exact powSub_mono (A := A) (B := ⊤) le_top)
  have hcard' : Nat.card ↥(omega1 P) = (Nat.card ↥(omega1 P)) ^ 2 := by
    rw [hA] at hcard
    exact hcard
  have h4 := h.omega1_card_ge_four
  have hpos : 0 < Nat.card ↥(omega1 P) := Nat.card_pos
  nlinarith

/-! ## The remaining gap: what the `C₄` case gives

In the branch `⁅A, ⊤⁆ = A ^ (2)` (the `C₄` case) the following facts hold, and they are all
that the exclusion can use:

* `A = P ^ (2) = ⁅P, P⁆` (`nsd_sq_eq`) and `A ^ (2) = Ω₁(P) = Z(P)`; `A` is homocyclic
  `(Z/4) ^ n` with `n = log₂ |Ω₁(P)|` (Higman's Lemma 1, `homogeneous_structure`),
* the squaring map descends to an `⟨ξ⟩`-equivariant map `f : P / A → A / A ^ (2)`
  (`nsd_coset_sq_wd`), whose image spans `A / A ^ (2)`,
* the commutator descends to an `⟨ξ⟩`-equivariant alternating biadditive pairing
  `β : P / A × P / A → A / A ^ (2)` with image all of `A / A ^ (2)` (since `[P,P] = A`),
* `Higman Lemma 2` gives: if `u ∉ A` and `[u,A] = 1` then `u ^ 2 ∉ A ^ (2)`.

Consequently (`nsd_exists_ord_eight`) the case forces an element of order `8`: were
`x ^ 4 = 1` for all `x`, then `A = P ^ (2) ≤ Ω₁(P) = A ^ (2)`, so `A = A ^ (2)` against
`|A| = |Ω₁(P)| ^ 2` and `|Ω₁(P)| ≥ 4`.  So *the lemma is exactly the statement that a Suzuki
2-group has exponent `4`*, i.e. `Φ(P) = Ω₁(P)`.  Higman's proof of that (`Φ = Ω₁ = Z = G'` in
every type) goes through Lemma 9 (`exp A ≤ 4` for maximal `A`) and the §6 classification; the
crucial intermediate result is Lemma 6: with `H` of class `3`, `ξ` of odd order irreducible on
`L₁ = H / H ^ (2) H'` and transitive on the non-zero vectors of `L₂ = H' / H'^2 H''` and
`L₂ ≅ L₃ = H'' / H''^2 H'''` under the squaring map, Lemma 6 (contradicting that isomorphism)
is what excludes the `C₄` shape via Lemma 8 with `C = ⊤`, and needs the `ξ`-eigenvalue
bookkeeping of §4 over a splitting field (a conjugate basis adapted to `ξ`).
-/

/-- `⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆`. -/
theorem commutator_mul_left_eq (x y z : P) :
    ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
  rw [commutatorElement_def]; group

/-- `⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹)`. -/
theorem commutator_mul_right_eq (x y z : P) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
  rw [commutatorElement_def]; group

/-- In the `C₄` case the commutator descends to `P / A × P / A → A / A ^ (2)`: changing `u`
and `v` by elements of `A` changes `⁅u, v⁆` by an element of `A ^ (2)`.  The extra hypothesis
`A ^ (2) ≤ Z(P)` holds in the application since `A ^ (2) = Ω₁(P) ⊆ Z(P)`. -/
theorem nsd_comm_pairing_wd (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hcen : powSub A 2 ≤ Subgroup.center P)
    (u v : P) {a b : P} (ha : a ∈ A) (hb : b ∈ A) :
    ⁅u * a, v * b⁆ * ⁅u, v⁆⁻¹ ∈ powSub A 2 := by
  have h2A : ∀ x ∈ A, ∀ y : P, ⁅x, y⁆ ∈ powSub A 2 := by
    intro x hx y
    have hmem : ⁅x, y⁆ ∈ ⁅A, (⊤ : Subgroup P)⁆ :=
      Subgroup.commutator_mem_commutator hx (Subgroup.mem_top y)
    exact nsd_comm_le h hAxi hAab hGs hmem
  have h2B : ∀ x : P, ∀ y ∈ A, ⁅x, y⁆ ∈ powSub A 2 := by
    intro x y hy
    have hmem : ⁅x, y⁆ ∈ ⁅(⊤ : Subgroup P), A⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) hy
    have hmem' : ⁅x, y⁆ ∈ ⁅A, (⊤ : Subgroup P)⁆ := by
      rwa [Subgroup.commutator_comm] at hmem
    exact nsd_comm_le h hAxi hAab hGs hmem'
  -- elements of `A ^ (2)` are central, so conjugation fixes them
  have hcen' : ∀ X ∈ powSub A 2, ∀ y : P, y * X * y⁻¹ = X := by
    intro X hX y
    have hc : Commute X y := (Subgroup.mem_center_iff.mp (hcen hX) y).symm
    calc y * X * y⁻¹ = y * (X * y⁻¹) := by group
      _ = y * (y⁻¹ * X) := by rw [(hc.inv_right).eq]
      _ = X := by group
  have hX : ⁅a, v * b⁆ ∈ powSub A 2 := h2A a ha (v * b)
  have hY : ⁅u, b⁆ ∈ powSub A 2 := h2B u b hb
  have hkey : ⁅u * a, v * b⁆ = ⁅a, v * b⁆ * (⁅u, v⁆ * ⁅u, b⁆) := by
    have e1 : ⁅u * a, v * b⁆ = u * ⁅a, v * b⁆ * u⁻¹ * ⁅u, v * b⁆ :=
      commutator_mul_left_eq u a (v * b)
    have e2 : u * ⁅a, v * b⁆ * u⁻¹ = ⁅a, v * b⁆ := hcen' _ hX u
    have e3 : ⁅u, v * b⁆ = ⁅u, v⁆ * (v * ⁅u, b⁆ * v⁻¹) := commutator_mul_right_eq u v b
    have e4 : v * ⁅u, b⁆ * v⁻¹ = ⁅u, b⁆ := hcen' _ hY v
    rw [e1, e2, e3, e4]
  have hmul : ⁅u * a, v * b⁆ * ⁅u, v⁆⁻¹ = ⁅a, v * b⁆ * ⁅u, b⁆ := by
    rw [hkey]
    have hc : Commute ⁅u, b⁆ ⁅u, v⁆ := (Subgroup.mem_center_iff.mp (hcen hY) ⁅u, v⁆).symm
    calc (⁅a, v * b⁆ * (⁅u, v⁆ * ⁅u, b⁆)) * ⁅u, v⁆⁻¹
        = ⁅a, v * b⁆ * (⁅u, v⁆ * (⁅u, b⁆ * ⁅u, v⁆⁻¹)) := by group
      _ = ⁅a, v * b⁆ * (⁅u, v⁆ * (⁅u, v⁆⁻¹ * ⁅u, b⁆)) := by rw [(hc.inv_right).eq]
      _ = ⁅a, v * b⁆ * ⁅u, b⁆ := by group
  rw [hmul]
  exact Subgroup.mul_mem _ hX hY

/-- In the `C₄` case the map `a ↦ ⁅a, u⁆` is a homomorphism `A → A ^ (2) ⊆ A`:
`⁅a * b, u⁆ = ⁅b, u⁆ * ⁅a, u⁆` for `a, b ∈ A` (this is the additivity of the pairing
`A/A ^ (2) → A ^ (2)` used to build the `⟨ξ⟩`-equivariant map `U → Hom(A/A ^ (2), A ^ (2))`). -/
theorem nsd_phi_mul (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (u : P) {a b : P} (ha : a ∈ A) (hb : b ∈ A) :
    ⁅a * b, u⁆ = ⁅b, u⁆ * ⁅a, u⁆ := by
  have hbu : ⁅b, u⁆ ∈ A := by
    rw [← hGs]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top b) (Subgroup.mem_top u)
  have hc : a * ⁅b, u⁆ * a⁻¹ = ⁅b, u⁆ := by
    have hcomm : Commute ⁅b, u⁆ a := hAab ⁅b, u⁆ hbu a ha
    calc a * ⁅b, u⁆ * a⁻¹ = a * (⁅b, u⁆ * a⁻¹) := by group
      _ = a * (a⁻¹ * ⁅b, u⁆) := by rw [(hcomm.inv_right).eq]
      _ = ⁅b, u⁆ := by group
  rw [commutator_mul_left_eq, hc]

/-- In the `C₄` case an element of `C_P(A) ∖ A` has square outside `A ^ (2)` — this is Higman's
Lemma 2 (`higman_lemma2`) specialized to `A ^ (4) = 1`, and it says that the squaring map
`f : P/A → A/A ^ (2)` is injective on the `ξ`-submodule `C_P(A)/A`. -/
theorem nsd_cent_sq (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hNA : omega1 P ≤ A) (hA4 : powSub A 4 = ⊥)
    {u : P} (huC : ∀ a ∈ A, u * a = a * u) (hu : u ∉ A) :
    u ^ 2 ∉ powSub A 2 := by
  intro hu2
  have hA : IsXiAbelNormal h A := ⟨nsd_normal hGs, hAxi, hAab⟩
  have hAne : A ≠ ⊥ := by
    intro hbot
    have hb : omega1 P = ⊥ := le_bot_iff.mp (hbot ▸ hNA)
    have hcard : Nat.card ↥(omega1 P) = 1 := by rw [hb]; simp
    have h4 := h.omega1_card_ge_four
    omega
  refine higman_lemma2 h hA hNA hAne hu ⟨hu2, fun a ha => ?_⟩
  have hone : ⁅u, a⁆ = 1 := by
    rw [commutatorElement_def, huC a ha]
    group
  rw [hone, hA4]
  exact Subgroup.mem_bot.mpr rfl

/-- **The squaring map is injective on the abelian subgroups containing `A`.**  In the `C₄` case,
if `A ≤ C ≤ P` with `C` abelian, then for `u, v ∈ C` with `u ^ 2 * (v ^ 2)⁻¹ ∈ A ^ (2)` one has
`u * v⁻¹ ∈ A`.

Indeed `w = u * v⁻¹ ∈ C` satisfies `w ^ 2 = u ^ 2 * (v ^ 2)⁻¹ ∈ A ^ (2)` (as `C` is abelian), and
`w` commutes with `A` (again as `C` is abelian), so Higman's Lemma 2 (`nsd_cent_sq`) forces
`w ∈ A`.  Consequently `|C / A| ≤ |A / A ^ (2)| = |Ω₁(P)|`: every abelian normal `ξ`-subgroup
containing `A` has order at most `|Ω₁(P)| ^ 3`. -/
theorem nsd_sq_inj_of_abelian (h : IsSuzuki2Grp P) {A C : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hNA : omega1 P ≤ A) (hA4 : powSub A 4 = ⊥) (hAC : A ≤ C)
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    {u v : P} (hu : u ∈ C) (hv : v ∈ C)
    (huv : u ^ 2 * (v ^ 2)⁻¹ ∈ powSub A 2) :
    u * v⁻¹ ∈ A := by
  by_contra hw
  have hwC : u * v⁻¹ ∈ C := C.mul_mem hu (C.inv_mem hv)
  have hw2 : (u * v⁻¹) ^ 2 = u ^ 2 * (v ^ 2)⁻¹ := by
    have hcuv : Commute v u := hCab v hv u hu
    have hcu : v⁻¹ * u = u * v⁻¹ := hcuv.inv_left.eq
    calc (u * v⁻¹) ^ 2 = (u * v⁻¹) * (u * v⁻¹) := pow_two _
      _ = u * (v⁻¹ * u) * v⁻¹ := by group
      _ = u * (u * v⁻¹) * v⁻¹ := by rw [hcu]
      _ = (u * u) * (v⁻¹ * v⁻¹) := by group
      _ = u ^ 2 * (v ^ 2)⁻¹ := by rw [pow_two, pow_two, mul_inv_rev]
  exact (nsd_cent_sq h hAxi hAab hGs hNA hA4 (fun a ha => hCab _ hwC _ (hAC ha)) hw)
    (hw2 ▸ huv)

/-- Contrapositive form of `nsd_sq_inj_of_abelian`: inside an abelian subgroup `C ≥ A` of the
`C₄` case, distinct cosets of `A` have distinct squares modulo `A ^ (2)` (so the fibres of
`f : P/A → A/A ^ (2)` meet `C/A` in at most one point). -/
theorem nsd_sq_ne_of_abelian (h : IsSuzuki2Grp P) {A C : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hNA : omega1 P ≤ A) (hA4 : powSub A 4 = ⊥) (hAC : A ≤ C)
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    {u v : P} (hu : u ∈ C) (hv : v ∈ C) (huv : u * v⁻¹ ∉ A) :
    u ^ 2 * (v ^ 2)⁻¹ ∉ powSub A 2 :=
  fun hmem => huv (nsd_sq_inj_of_abelian h hAxi hAab hGs hNA hA4 hAC hCab hu hv hmem)

/-- In the `C₄` case the squaring map `f : P/A → A/A ^ (2)` is not identically zero: some
element has square outside `A ^ (2)` (equivalently, some element has order `8`). -/
theorem nsd_f_ne_zero (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : powSub A 2 = omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(omega1 P)) ^ 2) :
    ∃ u : P, u ^ 2 ∉ powSub A 2 := by
  obtain ⟨u, hu⟩ := nsd_exists_ord_eight h hGs hsq htop hcard
  refine ⟨u, fun hmem => hu ?_⟩
  have h2 : u ^ 4 = (u ^ 2) ^ 2 := by simpa using (pow_mul u 2 2)
  rw [h2]
  exact h.mem_omega1.mp (by rwa [htop] at hmem)

/-! ## Towards Higman's Lemma 6 in the `C₄` case

Higman's Lemma 6 (applied through Lemma 8 with `C = ⊤`) is what excludes the `C₄` shape.  Its
first ingredient in our setting is the following: the commutator pairing `β` is *cyclically*
trivial — if `u ∈ C_P(A)` then `β(u, ·)` vanishes on the `𝔽₂[ξ]`-span of the coset `uA`, i.e.
`⁅u, ξ ^ k u⁆ ∈ A ^ (2)` for all `k`.

Note the elementary proof uses only `A` abelian with `[u, A] = [w, A] = 1`, `A = [P,P]`,
`A ^ (2) = Ω₁(P)` and `w ^ 2 ∈ A`: `[u, w ^ 2] = 1`, while `[u, w ^ 2] = [u,w] * (w [u,w] w⁻¹)
= [u,w] ^ 2` because `[u,w] ∈ A` is centralized by `w`; hence `[u,w] ^ 2 = 1` and
`[u,w] ∈ Ω₁(P) ∩ A = A ^ (2)`. -/

/-- If `u` and `w` both commute with `A`, then `⁅u, w⁆ ∈ A ^ (2)`. -/
theorem nsd_comm_eq_sq_of_comm (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (htop : powSub A 2 = omega1 P) (hsq : ∀ x : P, x ^ 2 ∈ A)
    (u w : P) (hu : ∀ a ∈ A, u * a = a * u) (hw : ∀ a ∈ A, w * a = a * w) :
    ⁅u, w⁆ ∈ powSub A 2 := by
  have hw2A : w ^ 2 ∈ A := hsq w
  have huwA : ⁅u, w⁆ ∈ A := by
    rw [← hGs]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top w)
  have h1 : ⁅u, w ^ 2⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hu (w ^ 2) hw2A)
  have h2 : ⁅u, w * w⁆ = ⁅u, w⁆ * (w * ⁅u, w⁆ * w⁻¹) := commutator_mul_right_eq u w w
  have h3 : w * ⁅u, w⁆ * w⁻¹ = ⁅u, w⁆ := by
    have hc : w * ⁅u, w⁆ = ⁅u, w⁆ * w := hw ⁅u, w⁆ huwA
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have h4 : ⁅u, w ^ 2⁆ = ⁅u, w⁆ ^ 2 := by
    rw [pow_two (a := w), h2, h3, pow_two]
  have h5 : ⁅u, w⁆ ^ 2 = 1 := by rw [← h4]; exact h1
  have hmem : ⁅u, w⁆ ∈ omega1 P ∧ ⁅u, w⁆ ∈ A := ⟨h.mem_omega1.mpr h5, huwA⟩
  rw [← htop] at hmem
  exact hmem.1

/-- `A` is invariant under every power of `ξ`. -/
theorem nsd_map_xi_pow_eq (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A) (k : ℕ) :
    A.map ((h.xi ^ k : MulAut P)).toMonoidHom = A := by
  induction k with
  | zero =>
    rw [show ((h.xi ^ 0 : MulAut P)) = 1 from pow_zero _]
    ext x; simp
  | succ k ih =>
    rw [pow_succ]
    have hcomp : (((h.xi ^ k) * h.xi : MulAut P)).toMonoidHom
        = ((h.xi ^ k : MulAut P)).toMonoidHom.comp (h.xi : MulAut P).toMonoidHom := by
      ext x; simp [MulAut.mul_apply]
    rw [hcomp, ← Subgroup.map_map, hAxi, ih]

/-- **Sub-case 2 payoff.**  In the `C₄` case, if a single element `u` commuting with `A`
generates `P` together with `A` and the `ξ`-orbit of `u`, then the whole derived subgroup lies
in `A ^ (2)`, contradicting `[P,P] = A` (since `|A| = |Ω₁(P)| ^ 2 ≠ |Ω₁(P)| = |A ^ (2)|`).

The proof repeats `nsd_comm_eq_sq_closure`'s subgroup argument in the *first* variable: the set
`{x | ∀ y, ⁅x, y⁆ ∈ A ^ (2)}` is a subgroup (using `[xy,z] = [x,z]·y[x,z]y⁻¹·...` with
`[b,y]` central), contains `A` (as `[A,P] ≤ A ^ (2)`) and the `ξ`-orbit of `u` (as
`⁅ξ ^ k u, y⁆ = ξ ^ k ⁅u, ξ ^ (-k) y⁆` and `A ^ (2) = Ω₁(P)` is `ξ`-invariant). -/
theorem nsd_comm_le_sq_of_generator (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (htop : powSub A 2 = omega1 P) (hsq : ∀ x : P, x ^ 2 ∈ A)
    (u : P) (huni : ∀ y : P, ⁅u, y⁆ ∈ powSub A 2)
    (hgen : ∀ x : P, x ∈ Subgroup.closure (↑A ∪ Set.range (fun k : ℕ => (h.xi ^ k) u))) :
    ∀ x y : P, ⁅x, y⁆ ∈ powSub A 2 := by
  have hA2Z : powSub A 2 ≤ Subgroup.center P := by
    rw [htop]; exact h.omega1_le_center
  have hcent : ∀ X ∈ powSub A 2, ∀ y : P, y * X * y⁻¹ = X := by
    intro X hX y
    have hc : Commute X y := (Subgroup.mem_center_iff.mp (hA2Z hX) y).symm
    calc y * X * y⁻¹ = y * (X * y⁻¹) := by group
      _ = y * (y⁻¹ * X) := by rw [(hc.inv_right).eq]
      _ = X := by group
  have hA2inv : ∀ z ∈ powSub A 2, ∀ k : ℕ, (h.xi ^ k) z ∈ powSub A 2 := by
    intro z hz k
    have hmap := map_powSub (h.xi ^ k) (nsd_map_xi_pow_eq h hAxi k) 2
    have hmem : (h.xi ^ k) z ∈ (powSub A 2).map ((h.xi ^ k : MulAut P)).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hz
    rwa [hmap] at hmem
  have hs : ∀ x ∈ (↑A ∪ Set.range (fun k : ℕ => (h.xi ^ k) u)), ∀ y : P, ⁅x, y⁆ ∈ powSub A 2 := by
    intro x hx y
    rcases hx with hxA | ⟨k, rfl⟩
    · have hmem : ⁅x, y⁆ ∈ ⁅A, (⊤ : Subgroup P)⁆ :=
        Subgroup.commutator_mem_commutator hxA (Subgroup.mem_top y)
      exact nsd_comm_le h hAxi hAab hGs hmem
    · have h1 : (h.xi ^ k : MulAut P) ⁅u, ((h.xi ^ k : MulAut P)).symm y⁆
          = ⁅(h.xi ^ k) u, y⁆ := by
        have hmap := map_commutatorElement (f := ((h.xi ^ k : MulAut P) : P →* P)) (g₁ := u)
          (g₂ := ((h.xi ^ k : MulAut P)).symm y)
        simpa using hmap
      rw [← h1]
      exact hA2inv _ (huni _) k
  intro x y
  refine Subgroup.closure_induction (p := fun z _ => ⁅z, y⁆ ∈ powSub A 2) ?_ ?_ ?_ ?_ (hgen x)
  · intro z hz
    exact hs z hz y
  · rw [commutatorElement_one_left]
    exact Subgroup.one_mem _
  · intro a b _ _ iha ihb
    rw [commutator_mul_left_eq a b y, hcent _ ihb]
    exact Subgroup.mul_mem _ ihb iha
  · intro a _ iha
    have h1 : ⁅a⁻¹, y⁆ = (⁅a, y⁆)⁻¹ := by
      rw [commutatorElement_inv_left, commutatorElement_inv]
      simpa using hcent (⁅a, y⁆⁻¹) (Subgroup.inv_mem _ iha) a⁻¹
    rw [h1]
    exact Subgroup.inv_mem _ iha

/-- **Sub-case 2 step: `β` is cyclically trivial.**  In the `C₄` case, if `u` commutes with `A`
then `⁅u, v⁆ ∈ A ^ (2)` for every `v` in the subgroup generated by `A` and the `ξ`-orbit of
`u`.  Equivalently, the commutator pairing `β : P/A × P/A → A/A ^ (2)` vanishes on the
`𝔽₂[ξ]`-span of the coset `uA`.

This is the "cyclicity" step of Higman's Lemma 6: the set `{v | ⁅u, v⁆ ∈ A ^ (2)}` is a subgroup
(it contains `A`, is closed under multiplication because `[u,xy] = [u,x]·x[u,y]x⁻¹ = [u,x]·[u,y]`
with `[u,y]` central, and under inverses), and it contains the `ξ`-orbit of `u` by
`nsd_comm_eq_sq_of_comm` (the orbit of `u` also commutes with `A`, as `A` and `C_P(A)` are
`ξ`-invariant). -/
theorem nsd_comm_eq_sq_closure (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (htop : powSub A 2 = omega1 P) (hsq : ∀ x : P, x ^ 2 ∈ A)
    (u : P) (hu : ∀ a ∈ A, u * a = a * u)
    {v : P} (hv : v ∈ Subgroup.closure (↑A ∪ Set.range (fun k : ℕ => (h.xi ^ k) u))) :
    ⁅u, v⁆ ∈ powSub A 2 := by
  -- `A ^ (2)` is central, so conjugation fixes its elements
  have hA2Z : powSub A 2 ≤ Subgroup.center P := by
    rw [htop]; exact h.omega1_le_center
  have hcent : ∀ X ∈ powSub A 2, ∀ y : P, y * X * y⁻¹ = X := by
    intro X hX y
    have hc : Commute X y := (Subgroup.mem_center_iff.mp (hA2Z hX) y).symm
    calc y * X * y⁻¹ = y * (X * y⁻¹) := by group
      _ = y * (y⁻¹ * X) := by rw [(hc.inv_right).eq]
      _ = X := by group
  -- `A` is invariant under every power of `ξ`
  have hinv_k : ∀ k : ℕ, A.map ((h.xi ^ k : MulAut P)).toMonoidHom = A := by
    intro k
    induction k with
    | zero =>
      rw [show ((h.xi ^ 0 : MulAut P)) = 1 from pow_zero _]
      ext x; simp
    | succ k ih =>
      rw [pow_succ]
      have hcomp : (((h.xi ^ k) * h.xi : MulAut P)).toMonoidHom
          = ((h.xi ^ k : MulAut P)).toMonoidHom.comp (h.xi : MulAut P).toMonoidHom := by
        ext x; simp [MulAut.mul_apply]
      rw [hcomp, ← Subgroup.map_map, hAxi, ih]
  -- the `ξ`-orbit of `u` also commutes with `A`
  have hK : ∀ k : ℕ, ∀ a ∈ A, ((h.xi ^ k) u) * a = a * ((h.xi ^ k) u) := by
    intro k a ha
    have hsymm : ((h.xi ^ k : MulAut P)).symm a ∈ A :=
      symm_mem_of_map_eq (h.xi ^ k) (hinv_k k) ha
    have h1 : u * (((h.xi ^ k : MulAut P)).symm a) = (((h.xi ^ k : MulAut P)).symm a) * u :=
      hu _ hsymm
    have h2 := congrArg (fun t : P => (h.xi ^ k : MulAut P) t) h1
    simpa using h2
  -- the generators are in the set
  have hgen : ∀ w ∈ (↑A ∪ Set.range (fun k : ℕ => (h.xi ^ k) u)), ⁅u, w⁆ ∈ powSub A 2 := by
    intro w hw
    rcases hw with hwA | ⟨k, rfl⟩
    · rw [commutatorElement_eq_one_iff_mul_comm.mpr (hu w hwA)]
      exact Subgroup.one_mem _
    · exact nsd_comm_eq_sq_of_comm h hAab hGs htop hsq u _ hu (hK k)
  induction hv using Subgroup.closure_induction with
  | mem y hy => exact hgen y hy
  | one =>
    rw [commutatorElement_one_right]
    exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    rw [commutator_mul_right_eq u x y, hcent ⁅u, y⁆ ihy]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ihx =>
    have hx' : ⁅u, x⁻¹⁆ = (⁅u, x⁆)⁻¹ := by
      rw [commutatorElement_inv_right, ← commutatorElement_inv]
      simpa using hcent (⁅u, x⁆⁻¹) (Subgroup.inv_mem _ ihx) x⁻¹
    rw [hx']
    exact Subgroup.inv_mem _ ihx

/-- **Sub-case 2 endgame.**  In the `C₄` case, if every commutator of `P` lies in `A ^ (2)`,
then `A = [P,P] ⊆ A ^ (2)`, whence `A = Ω₁(P)`, contradicting `|A| = |Ω₁(P)| ^ 2 ≥ 16`. -/
theorem nsd_false_of_comm_le_sq (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (htop : powSub A 2 = omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(omega1 P)) ^ 2)
    (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ powSub A 2) :
    False := by
  have hle' : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ powSub A 2 :=
    Subgroup.commutator_le.mpr (fun x _ y _ => hcomm x y)
  have hle : A ≤ powSub A 2 := hGs ▸ hle'
  have hA2 : A = powSub A 2 := le_antisymm hle (powSub_le (A := A) (n := 2) (by norm_num))
  have hΩ : omega1 P = A := htop.symm.trans hA2.symm
  have hcard' : Nat.card ↥A = (Nat.card ↥A) ^ 2 := by
    rw [hΩ] at hcard
    exact hcard
  have h4 : 4 ≤ Nat.card ↥A := by
    rw [← hΩ]
    exact h.omega1_card_ge_four
  nlinarith [hcard', h4]

/-- **Sub-case 2.**  In the `C₄` case, if a single element `u` commuting with `A` generates `P`
together with `A` and the `ξ`-orbit of `u` (i.e. the coset `uA` generates `P/A` as an
`𝔽₂[ξ]`-module), then we reach a contradiction: the derived subgroup lies in `A ^ (2)` by
`nsd_comm_eq_sq_closure` + `nsd_comm_le_sq_of_generator`, forcing `A = Ω₁(P)`. -/
theorem nsd_false_of_single_generator (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (htop : powSub A 2 = omega1 P) (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hcard : Nat.card ↥A = (Nat.card ↥(omega1 P)) ^ 2)
    (u : P) (hu : ∀ a ∈ A, u * a = a * u)
    (hgen : ∀ x : P, x ∈ Subgroup.closure (↑A ∪ Set.range (fun k : ℕ => (h.xi ^ k) u))) :
    False := by
  have huni : ∀ y : P, ⁅u, y⁆ ∈ powSub A 2 := fun y =>
    nsd_comm_eq_sq_closure h hAxi hAab hGs htop hsq u hu (hgen y)
  exact nsd_false_of_comm_le_sq h hGs htop hcard
    (nsd_comm_le_sq_of_generator h hAxi hAab hGs htop hsq u huni hgen)

/-- **Assembly with the exponent-`4` statement.**  If in the `C₄` case every element of `P` has
`x ^ 4 = 1` (i.e. `P` has exponent `4`, Higman's theorem `Φ(P) = Ω₁(P)`), then `A = P ^ (2)`
lies in `Ω₁(P) = A ^ (2)`, so `A = A ^ (2)` and `|A| = |A ^ (2)| = |Ω₁(P)|` contradicts
`|A| = |Ω₁(P)| ^ 2 ≥ 16`. -/
theorem nsd_false_of_exp_four (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : powSub A 2 = omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(omega1 P)) ^ 2)
    (hexp : ∀ x : P, x ^ 4 = 1) : False := by
  have hle : powSub (⊤ : Subgroup P) 2 ≤ omega1 P := by
    rw [powSub, Subgroup.closure_le]
    rintro y ⟨x, -, rfl⟩
    refine h.mem_omega1.mpr ?_
    have h2 : x ^ 4 = (x ^ 2) ^ 2 := by simpa using (pow_mul x 2 2)
    rw [← h2]
    exact hexp x
  have hA' : A ≤ omega1 P := by
    rw [← nsd_sq_eq h hGs hsq]
    exact hle
  have hA : A ≤ powSub A 2 := by
    rw [htop]
    exact hA'
  refine nsd_false_of_comm_le_sq h hGs htop hcard (fun x y => ?_)
  exact hA (by
    rw [← hGs]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))

end Work.Higman.H8.Clean
