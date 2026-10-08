import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.powSub_normal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped commutatorElement

namespace Work.Higman

/-! ## Auxiliary group theory

Two elementary facts are collected here: the commutator identity used to advance the lower
central series of `C` by squaring, and the `ξ`-abelian-normality of power subgroups. -/

/-- The commutator identity `⁅b,c⁆ ^ 2 = ⁅b, c ^ 2⁆ * ⁅c, ⁅b,c⁆⁻¹⁆`, valid in any group
(with Mathlib's convention `⁅x,y⁆ = x*y*x⁻¹*y⁻¹`). -/
private theorem commutator_sq_eq {P : Type} [Group P] (b c : P) :
    ⁅b, c⁆ ^ 2 = ⁅b, c ^ 2⁆ * ⁅c, ⁅b, c⁆⁻¹⁆ := by
  simp only [commutatorElement_def, pow_two]
  group

/-- **Unipotence**, in the form used below: for a `ξ`-invariant abelian normal subgroup `A`,
`⁅A, C⁆ ≤ A ^ (2)`. -/
private theorem commutator_le_powSub_two {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P)
    {A C : Subgroup P} (hA : IsXiAbelNormal h A) : ⁅A, C⁆ ≤ powSub A 2 := by
  rw [Subgroup.commutator_comm, Subgroup.commutator_le]
  intro u _ a ha
  exact commutator_mem_powSub_two h hA u a ha

/-- A power subgroup of a `ξ`-invariant abelian normal subgroup is again `ξ`-invariant,
abelian and normal. -/
private theorem isXiAbelNormal_powSub {P : Type} [Group P] [Finite P] {h : IsSuzuki2Grp P}
    {A : Subgroup P} (hA : IsXiAbelNormal h A) (n : ℕ) : IsXiAbelNormal h (powSub A n) :=
  ⟨powSub_normal hA.normal n, map_powSub (h.xi : MulAut P) hA.map_eq n, powSub_comm hA.abelian n⟩

/-- **Squaring advances the lower central series of a subgroup by one step.**
Let `C` be a subgroup of a group with `C ^ (2) ≤ ⁅C,C⁆` and `⁅C,C⁆` abelian.  Then for every `n`
the square subgroup of the `n`-th term of the lower central series of `C` (Mathlib's
`C.lowerCentralSeries`, so `γ₀ = C`, `γ_{n+1} = ⁅γ_n, C⁆`) is contained in the next term:
`(γ_n) ^ (2) ≤ γ_{n+1}`.

For a generator `s = ⁅b,c⁆` of `γ_{m+1}` (`b ∈ γ_m`, `c ∈ C`) the identity
`commutator_sq_eq` reads `s ^ 2 = ⁅b, c ^ 2⁆ * ⁅c, s⁻¹⁆`; here `⁅c, s⁻¹⁆ ∈ ⁅C, γ_{m+1}⁆ = γ_{m+2}`
and `⁅b, c ^ 2⁆` lies in `γ_{m+2}` as well — for `m = 0` because `c ^ 2 ∈ C ^ (2) ≤ ⁅C,C⁆ = γ₁`,
and for `m ≥ 1` because `b ∈ γ_m ≤ γ₁ = ⁅C,C⁆` is abelian and `c ^ 2 ∈ ⁅C,C⁆`, so `⁅b,c ^ 2⁆ = 1`.
Since `γ_{m+1} ≤ γ₁ = ⁅C,C⁆` is abelian, this extends to all of `γ_{m+1}`. -/
private theorem lowerCentralSeries_powSub_le {P : Type} [Group P] (C : Subgroup P) (hCn : C.Normal)
    (hC2 : powSub C 2 ≤ ⁅C, C⁆)
    (hab : ∀ x ∈ ⁅C, C⁆, ∀ y ∈ ⁅C, C⁆, x * y = y * x) :
    ∀ n : ℕ, powSub (C.lowerCentralSeries n) 2 ≤ C.lowerCentralSeries (n + 1) := by
  have hγ1 : C.lowerCentralSeries 1 = ⁅C, C⁆ := by
    have h := Subgroup.lowerCentralSeries_succ C 0
    rw [Subgroup.lowerCentralSeries_zero] at h
    exact h
  have hmono : ∀ {j : ℕ}, 1 ≤ j → C.lowerCentralSeries j ≤ ⁅C, C⁆ := by
    intro j hj
    rw [← hγ1]
    exact Subgroup.lowerCentralSeries_antitone C hj
  -- every square of an element of `γ_n` lies in `γ_{n+1}`
  have key : ∀ n, ∀ x ∈ C.lowerCentralSeries n, x ^ 2 ∈ C.lowerCentralSeries (n + 1) := by
    intro n
    induction n with
    | zero =>
        intro x hx
        have hx2 : x ^ 2 ∈ powSub C 2 := pow_mem_powSub hx
        have hmem : x ^ 2 ∈ ⁅C, C⁆ := hC2 hx2
        show x ^ 2 ∈ C.lowerCentralSeries 1
        rw [hγ1]
        exact hmem
    | succ m _ih =>
        intro x hx
        rw [Subgroup.lowerCentralSeries_succ] at hx
        have keym : C.lowerCentralSeries (m + 1 + 1) = ⁅C, C.lowerCentralSeries (m + 1)⁆ := by
          rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
        have habγ : ∀ a ∈ C.lowerCentralSeries (m + 1), ∀ b ∈ C.lowerCentralSeries (m + 1),
            a * b = b * a :=
          fun a ha b hb => hab a (hmono (j := m + 1) (by omega) ha)
            b (hmono (j := m + 1) (by omega) hb)
        have hgen : ∀ p ∈ C.lowerCentralSeries m, ∀ q ∈ C,
            (⁅p, q⁆ : P) ^ 2 ∈ C.lowerCentralSeries (m + 1 + 1) := by
          intro p hp q hq
          have hq2 : q ^ 2 ∈ ⁅C, C⁆ := hC2 (pow_mem_powSub hq)
          have hA : ⁅p, q ^ 2⁆ ∈ C.lowerCentralSeries (m + 1 + 1) := by
            rcases Nat.eq_zero_or_pos m with hm | hm
            · subst hm
              rw [Subgroup.lowerCentralSeries_zero] at hp
              have key0 : C.lowerCentralSeries (0 + 1 + 1) = ⁅⁅C, C⁆, C⁆ := by
                have h1 : C.lowerCentralSeries (1 + 1) = ⁅C.lowerCentralSeries 1, C⁆ :=
                  Subgroup.lowerCentralSeries_succ C 1
                rw [hγ1] at h1
                exact h1
              rw [key0, Subgroup.commutator_comm]
              exact Subgroup.commutator_mem_commutator hp hq2
            · have hpm : p ∈ ⁅C, C⁆ := hmono (j := m) (by omega) hp
              have hone : ⁅p, q ^ 2⁆ = 1 := by
                rw [commutatorElement_eq_one_iff_mul_comm]
                exact hab p hpm (q ^ 2) hq2
              rw [hone]
              exact (C.lowerCentralSeries (m + 1 + 1)).one_mem
          have hB : ⁅q, ⁅p, q⁆⁻¹⁆ ∈ C.lowerCentralSeries (m + 1 + 1) := by
            rw [keym]
            have hs : ⁅p, q⁆ ∈ C.lowerCentralSeries (m + 1) :=
              Subgroup.commutator_mem_commutator hp hq
            exact Subgroup.commutator_mem_commutator hq (Subgroup.inv_mem _ hs)
          rw [commutator_sq_eq p q]
          exact Subgroup.mul_mem _ hA hB
        have hxc : x ∈ Subgroup.closure
            {g : P | ∃ g₁ ∈ C.lowerCentralSeries m, ∃ g₂ ∈ C, ⁅g₁, g₂⁆ = g} := hx
        refine Subgroup.closure_induction
          (p := fun z (_ : z ∈ ⁅C.lowerCentralSeries m, C⁆) =>
            z ^ 2 ∈ C.lowerCentralSeries (m + 1 + 1)) ?_ ?_ ?_ ?_ hxc
        · rintro y hy
          rcases hy with ⟨p, hp, q, hq, rfl⟩
          exact hgen p hp q hq
        · simpa using (C.lowerCentralSeries (m + 1 + 1)).one_mem
        · intro a b ha hb iha ihb
          have hc : Commute a b := habγ a ha b hb
          rw [hc.mul_pow 2]
          exact Subgroup.mul_mem _ iha ihb
        · intro a ha iha
          rw [inv_pow]
          exact Subgroup.inv_mem _ iha
  intro n
  rw [powSub, Subgroup.closure_le]
  rintro y ⟨x, hx, rfl⟩
  exact key n x hx

/-- **Higman 1963, Lemma 8 — step 3 (the lower central series of `C`).**  In the situation of
Higman's Lemma 8, with `C ^ (2) ≤ A = ⁅C,C⁆`, the lower central series of `C` is
`C > A > A² > A⁴ > ⋯`: the commutator of `A ^ (2 ^ k)` with `C` is `A ^ (2 ^ (k+1))`.

Ingredients (all available in the workspace; `A ≤ C` follows from `hCd`):
* **⊆**: `powSub A (2^k)` is a `ξ`-invariant abelian normal subgroup (it is `A ^ (2^k)`), so the
  unipotence lemma `Work.Higman.commutator_mem_powSub_two` (equivalently
  `commutator_A_C_le`) applies to *it*, giving `⁅A ^ (2^k), C⁆ ≤ (A ^ (2^k))² = A ^ (2^(k+1))`
  (`Work.Higman.powSub_powSub`).
* **⊇**: set `γ₁ = C`, `γ₂ = A = C'`, `γ_{j+1} = ⁅γ_j, C⁆`.  From `C ^ (2) ≤ γ₂` prove
  `γ_j ^ (2) ≤ γ_{j+1}` by induction on `j`: for a generator `s = ⁅b,c⁆` of `γ_j` use
  `⁅b, c²⁆ = ⁅b,c⁆² · ⁅⁅b,c⁆, c⁆`, where `c² ∈ C² ≤ A` makes `⁅b, c²⁆ ∈ γ_{j+1}` (it is `1` for
  `j ≥ 3`, as then `b, c² ∈ A` and `A` is abelian) and `⁅s,c⁆ ∈ γ_{j+1}`; since `γ_j ≤ A` is
  abelian, `γ_j² ≤ γ_{j+1}`.  Inductively `γ_{k+2} = A ^ (2^k)`, whence
  `A ^ (2^(k+1)) = γ_{k+2}² ≤ γ_{k+3} = ⁅A ^ (2^k), C⁆`. -/
theorem commutator_powSub_A_C {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A) (hCn : C.Normal)
    (hC2 : Work.Higman.powSub C 2 ≤ A) (hCd : ⁅C, C⁆ = A) :
    ∀ k : ℕ, ⁅Work.Higman.powSub A (2 ^ k), C⁆ = Work.Higman.powSub A (2 ^ (k + 1)) := by
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  have hC2' : powSub C 2 ≤ ⁅C, C⁆ := by rw [hCd]; exact hC2
  have hab : ∀ x ∈ ⁅C, C⁆, ∀ y ∈ ⁅C, C⁆, x * y = y * x := by
    intro x hx y hy
    rw [hCd] at hx hy
    exact hAb x hx y hy
  have hsquar := lowerCentralSeries_powSub_le C hCn hC2' hab
  -- the `⊆` direction
  have hle : ∀ k, ⁅powSub A (2 ^ k), C⁆ ≤ powSub A (2 ^ (k + 1)) := by
    intro k
    have hB : IsXiAbelNormal h (powSub A (2 ^ k)) := isXiAbelNormal_powSub hA (2 ^ k)
    have h1 : ⁅powSub A (2 ^ k), C⁆ ≤ powSub (powSub A (2 ^ k)) 2 :=
      commutator_le_powSub_two h hB
    have h2 : powSub (powSub A (2 ^ k)) 2 = powSub A (2 ^ (k + 1)) := by
      rw [powSub_powSub hAb, pow_succ]
    rwa [h2] at h1
  have hγ1 : C.lowerCentralSeries 1 = A := by
    have h := Subgroup.lowerCentralSeries_succ C 0
    rw [Subgroup.lowerCentralSeries_zero, hCd] at h
    exact h
  -- `A ^ (2 ^ k)` is bounded below by `γ_{k+1}`
  have hlow : ∀ k, powSub A (2 ^ k) ≤ C.lowerCentralSeries (k + 1) := by
    intro k
    induction k with
    | zero =>
        show powSub A (2 ^ 0) ≤ C.lowerCentralSeries 1
        rw [pow_zero, powSub_one_eq, hγ1]
    | succ k ih =>
        have hstep : powSub A (2 ^ (k + 1)) = powSub (powSub A (2 ^ k)) 2 := by
          rw [pow_succ, powSub_powSub hAb]
        rw [hstep]
        exact (powSub_mono ih).trans (hsquar (k + 1))
  -- `γ_{k+1}` is bounded below by `A ^ (2 ^ k)`
  have hup : ∀ k, C.lowerCentralSeries (k + 1) ≤ powSub A (2 ^ k) := by
    intro k
    induction k with
    | zero =>
        show C.lowerCentralSeries 1 ≤ powSub A (2 ^ 0)
        rw [hγ1, pow_zero, powSub_one_eq]
    | succ k ih =>
        have hstep : C.lowerCentralSeries (k + 1 + 1) = ⁅C.lowerCentralSeries (k + 1), C⁆ :=
          Subgroup.lowerCentralSeries_succ C (k + 1)
        rw [hstep]
        exact (Subgroup.commutator_mono_left ih).trans (hle k)
  intro k
  apply le_antisymm
  · exact hle k
  · have hEq : C.lowerCentralSeries (k + 1) = powSub A (2 ^ k) := le_antisymm (hup k) (hlow k)
    calc powSub A (2 ^ (k + 1))
        = powSub (powSub A (2 ^ k)) 2 := by rw [pow_succ, powSub_powSub hAb]
      _ = powSub (C.lowerCentralSeries (k + 1)) 2 := by rw [hEq]
      _ ≤ C.lowerCentralSeries (k + 1 + 1) := hsquar (k + 1)
      _ = ⁅C.lowerCentralSeries (k + 1), C⁆ := Subgroup.lowerCentralSeries_succ C (k + 1)
      _ = ⁅powSub A (2 ^ k), C⁆ := by rw [hEq]

end Work.Higman
