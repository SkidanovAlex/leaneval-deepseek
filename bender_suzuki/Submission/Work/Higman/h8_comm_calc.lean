import Mathlib
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.commutator_powSub_A_C

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

/-! ## General group-theoretic identities in a normal abelian subgroup

The six conjuncts of `h8_comm_calc` are of two kinds.

* Two are plain computations in a group `G` with a normal abelian subgroup `A`: for `a ∈ A` and
  `u : G` one has `(u a)² = u² a² · u⁻¹ (a u a⁻¹ u⁻¹) u`, and for `u, v : G` with `v² ∈ A` one has
  `(u v)² = u² v² · u⁻¹ v u v⁻¹`.  In both, the point is that `u² ∈ A` and `v² ∈ A` commute with
  everything in `A`, so the two sides agree after moving `u`-conjugation past the elements of `A`.
* The other four (and the second conjunct) assert that a commutator expression lies in `A ^ (2)`.
  Each reduces, by a standard commutator identity, to the *unipotence* statement
  `⁅x, y⁆ ∈ A ^ (2)` for `x : G`, `y ∈ A`, possibly conjugated by an element of `A` (which
  commutes with `A ^ (2) ⊆ A`).

We package the four membership statements as: `⁅u⁻¹, a⁆`, `⁅u⁻¹, ⁅v,u⁆⁆`, `⁅u, ⁅w,v⁆⁆`
(conjugated) and `⁅u, ⁅v,w⁆⁆` (conjugated). -/

/-- **Identity (1).**  In any group with a normal abelian subgroup `A`, for `a ∈ A` and any `u`:
`(u a)² = u² a² · u⁻¹ (a u a⁻¹ u⁻¹) u`. -/
private theorem h8cc_sq_mul_form {G : Type} [Group G] {A : Subgroup G} (hAn : A.Normal)
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {u a : G} (ha : a ∈ A) :
    (u * a) * (u * a) = (u * u) * (a * a) * (u⁻¹ * (a * u * a⁻¹ * u⁻¹) * u) := by
  have hb : u⁻¹ * a * u ∈ A := hAn.conj_mem' a ha u
  have hc : a * (u⁻¹ * a * u) = (u⁻¹ * a * u) * a := (hab (u⁻¹ * a * u) hb a ha).symm
  have key : (a * a) * ((u⁻¹ * a * u) * a⁻¹) = (u⁻¹ * a * u) * a := by
    calc (a * a) * ((u⁻¹ * a * u) * a⁻¹)
        = a * (a * (u⁻¹ * a * u)) * a⁻¹ := by group
      _ = a * ((u⁻¹ * a * u) * a) * a⁻¹ := by rw [hc]
      _ = a * (u⁻¹ * a * u) := by group
      _ = (u⁻¹ * a * u) * a := hc
  calc (u * a) * (u * a) = (u * u) * (u⁻¹ * a * u) * a := by group
    _ = (u * u) * (a * a) * (u⁻¹ * (a * u * a⁻¹ * u⁻¹) * u) := by
      rw [show u⁻¹ * (a * u * a⁻¹ * u⁻¹) * u = u⁻¹ * a * u * a⁻¹ from by group,
        mul_assoc (u * u) (a * a) (u⁻¹ * a * u * a⁻¹), key]
      group

/-- **Identity (3).**  In any group with a normal abelian subgroup `A`, for `u`, `v` with
`v * v ∈ A` and `⁅v,u⁆ ∈ A`: `(u v)² = u² v² · u⁻¹ v u v⁻¹`. -/
private theorem h8cc_sq_mul_form' {G : Type} [Group G] {A : Subgroup G} (hAn : A.Normal)
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {u v : G} (hv2 : v * v ∈ A)
    (hc : ⁅v, u⁆ ∈ A) :
    (u * v) * (u * v) = (u * u) * (v * v) * (u⁻¹ * v * u * v⁻¹) := by
  have hd : u⁻¹ * ⁅v, u⁆ * u ∈ A := hAn.conj_mem' _ hc u
  have hvu : v * u = ⁅v, u⁆ * (u * v) := by rw [commutatorElement_def]; group
  have hL : (u * v) * (u * v) = (u * u) * (u⁻¹ * ⁅v, u⁆ * u) * (v * v) := by
    rw [show (u * v) * (u * v) = u * (v * u) * v from by group, hvu]
    group
  have hR : (u * u) * (v * v) * (u⁻¹ * v * u * v⁻¹)
      = (u * u) * (v * v) * (u⁻¹ * ⁅v, u⁆ * u) := by
    rw [show u⁻¹ * v * u * v⁻¹ = u⁻¹ * (v * u) * v⁻¹ from by group, hvu]
    group
  calc (u * v) * (u * v) = (u * u) * (u⁻¹ * ⁅v, u⁆ * u) * (v * v) := hL
    _ = (u * u) * (v * v) * (u⁻¹ * ⁅v, u⁆ * u) := by
        rw [mul_assoc (u * u) (u⁻¹ * ⁅v, u⁆ * u) (v * v), hab _ hd _ hv2]
        group
    _ = (u * u) * (v * v) * (u⁻¹ * v * u * v⁻¹) := hR.symm

/-- **Conjunct (2).**  `u⁻¹ (a u a⁻¹ u⁻¹) u = ⁅u⁻¹, a⁆`, whose unipotence class is `A ^ (2)`. -/
private theorem h8cc_mem_two {G : Type} [Group G] {A : Subgroup G}
    (hunip : ∀ x : G, ∀ y ∈ A, ⁅x, y⁆ ∈ powSub A 2) {u a : G} (ha : a ∈ A) :
    u⁻¹ * (a * u * a⁻¹ * u⁻¹) * u ∈ powSub A 2 := by
  have e : u⁻¹ * (a * u * a⁻¹ * u⁻¹) * u = ⁅u⁻¹, a⁆ := by
    rw [commutatorElement_def]; group
  rw [e]
  exact hunip u⁻¹ a ha

/-- **Conjunct (4).**  `(u⁻¹ v u v⁻¹) (v u v⁻¹ u⁻¹)⁻¹ = ⁅u⁻¹, ⁅v,u⁆⁆ ∈ A ^ (2)`. -/
private theorem h8cc_mem_four {G : Type} [Group G] {A : Subgroup G}
    (hunip : ∀ x : G, ∀ y ∈ A, ⁅x, y⁆ ∈ powSub A 2) {u v : G} (hc : ⁅v, u⁆ ∈ A) :
    (u⁻¹ * v * u * v⁻¹) * (v * u * v⁻¹ * u⁻¹)⁻¹ ∈ powSub A 2 := by
  have hvu : v * u = ⁅v, u⁆ * (u * v) := by rw [commutatorElement_def]; group
  have h2 : u⁻¹ * v * u * v⁻¹ = u⁻¹ * ⁅v, u⁆ * u := by
    rw [show u⁻¹ * v * u * v⁻¹ = u⁻¹ * (v * u) * v⁻¹ from by group, hvu]
    group
  have h1 : v * u * v⁻¹ * u⁻¹ = ⁅v, u⁆ := by rw [commutatorElement_def]
  have e : (u⁻¹ * v * u * v⁻¹) * (v * u * v⁻¹ * u⁻¹)⁻¹ = ⁅u⁻¹, ⁅v, u⁆⁆ := by
    rw [h1, h2, commutatorElement_def]
    group
  rw [e]
  exact hunip u⁻¹ ⁅v, u⁆ hc

/-- **Conjunct (5).**  `[w, uv] · ([w,u][w,v])⁻¹ = [w,u] · [u,[w,v]] · [w,u]⁻¹`, and the middle
factor lies in `A ^ (2)` while the conjugating `[w,u]` lies in `A`. -/
private theorem h8cc_mem_five {G : Type} [Group G] {A : Subgroup G}
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hunip : ∀ x : G, ∀ y ∈ A, ⁅x, y⁆ ∈ powSub A 2)
    (hA2le : powSub A 2 ≤ A)
    {u v w : G} (ha : ⁅w, u⁆ ∈ A) (hb : ⁅w, v⁆ ∈ A) :
    (w * (u * v) * w⁻¹ * (u * v)⁻¹) * ((w * u * w⁻¹ * u⁻¹) * (w * v * w⁻¹ * v⁻¹))⁻¹
      ∈ powSub A 2 := by
  have h1 : w * (u * v) * w⁻¹ * (u * v)⁻¹ = ⁅w, u⁆ * (u * ⁅w, v⁆ * u⁻¹) := by
    simp only [commutatorElement_def]; group
  have h2 : (w * u * w⁻¹ * u⁻¹) * (w * v * w⁻¹ * v⁻¹) = ⁅w, u⁆ * ⁅w, v⁆ := by
    simp only [commutatorElement_def]
  have hk : ⁅u, ⁅w, v⁆⁆ ∈ powSub A 2 := hunip u ⁅w, v⁆ hb
  have hkA : ⁅u, ⁅w, v⁆⁆ ∈ A := hA2le hk
  have key : ⁅w, u⁆ * (u * ⁅w, v⁆ * u⁻¹) * (⁅w, u⁆ * ⁅w, v⁆)⁻¹ = ⁅u, ⁅w, v⁆⁆ := by
    rw [show u * ⁅w, v⁆ * u⁻¹ = ⁅u, ⁅w, v⁆⁆ * ⁅w, v⁆ from by
          rw [commutatorElement_def]; group]
    rw [show ⁅w, u⁆ * (⁅u, ⁅w, v⁆⁆ * ⁅w, v⁆) * (⁅w, u⁆ * ⁅w, v⁆)⁻¹
              = ⁅w, u⁆ * ⁅u, ⁅w, v⁆⁆ * ⁅w, u⁆⁻¹ from by group]
    rw [hab _ ha _ hkA]
    group
  have hgoal : (w * (u * v) * w⁻¹ * (u * v)⁻¹) * ((w * u * w⁻¹ * u⁻¹) * (w * v * w⁻¹ * v⁻¹))⁻¹
      = ⁅u, ⁅w, v⁆⁆ := by
    rw [h1, h2, key]
  rw [hgoal]
  exact hk

/-- **Conjunct (6).**  `[uv, w] · ([u,w][v,w])⁻¹ = [v,w]^u · [u,w] · ([u,w][v,w])⁻¹
= [u, [v,w]] ∈ A ^ (2)`. -/
private theorem h8cc_mem_six {G : Type} [Group G] {A : Subgroup G}
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hunip : ∀ x : G, ∀ y ∈ A, ⁅x, y⁆ ∈ powSub A 2)
    (hA2le : powSub A 2 ≤ A)
    {u v w : G} (ha : ⁅u, w⁆ ∈ A) (hb : ⁅v, w⁆ ∈ A) :
    ((u * v) * w * (u * v)⁻¹ * w⁻¹) * ((u * w * u⁻¹ * w⁻¹) * (v * w * v⁻¹ * w⁻¹))⁻¹
      ∈ powSub A 2 := by
  have h1 : (u * v) * w * (u * v)⁻¹ * w⁻¹ = (u * ⁅v, w⁆ * u⁻¹) * ⁅u, w⁆ := by
    simp only [commutatorElement_def]; group
  have h2 : (u * w * u⁻¹ * w⁻¹) * (v * w * v⁻¹ * w⁻¹) = ⁅u, w⁆ * ⁅v, w⁆ := by
    simp only [commutatorElement_def]
  have hk : ⁅u, ⁅v, w⁆⁆ ∈ powSub A 2 := hunip u ⁅v, w⁆ hb
  have hkA : ⁅u, ⁅v, w⁆⁆ ∈ A := hA2le hk
  have key : (u * ⁅v, w⁆ * u⁻¹) * ⁅u, w⁆ * (⁅u, w⁆ * ⁅v, w⁆)⁻¹ = ⁅u, ⁅v, w⁆⁆ := by
    rw [show u * ⁅v, w⁆ * u⁻¹ = ⁅u, ⁅v, w⁆⁆ * ⁅v, w⁆ from by
          rw [commutatorElement_def]; group]
    rw [show (⁅u, ⁅v, w⁆⁆ * ⁅v, w⁆) * ⁅u, w⁆ * (⁅u, w⁆ * ⁅v, w⁆)⁻¹
              = ⁅u, ⁅v, w⁆⁆ * (⁅v, w⁆ * ⁅u, w⁆) * ⁅v, w⁆⁻¹ * ⁅u, w⁆⁻¹ from by group]
    rw [hab _ hb _ ha]
    group
  have hgoal : ((u * v) * w * (u * v)⁻¹ * w⁻¹)
      * ((u * w * u⁻¹ * w⁻¹) * (v * w * v⁻¹ * w⁻¹))⁻¹ = ⁅u, ⁅v, w⁆⁆ := by
    rw [h1, h2, key]
  rw [hgoal]
  exact hk

/-- Group-theoretic commutator/squaring calculus for Higman's Lemma 8.  `A` is a normal abelian
`ξ`-subgroup of a Suzuki 2-group, `A ≤ C`, `C² ≤ A`, `⁅C,C⁆ = A`; unipotence `⁅A,C⁆ ≤ A²` is used.
The commutators are written out explicitly (`x * y * x⁻¹ * y⁻¹`). -/
theorem h8_comm_calc {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : IsXiAbelNormal h A) (hAC : A ≤ C) (hC2 : powSub C 2 ≤ A) (hCd : ⁅C, C⁆ = A) :
    (∀ u ∈ C, ∀ a ∈ A,
      (u * a) * (u * a) = (u * u) * (a * a) * (u⁻¹ * (a * u * a⁻¹ * u⁻¹) * u)) ∧
    (∀ u ∈ C, ∀ a ∈ A, u⁻¹ * (a * u * a⁻¹ * u⁻¹) * u ∈ powSub A 2) ∧
    (∀ u ∈ C, ∀ v ∈ C,
      (u * v) * (u * v) = (u * u) * (v * v) * (u⁻¹ * v * u * v⁻¹)) ∧
    (∀ u ∈ C, ∀ v ∈ C, (u⁻¹ * v * u * v⁻¹) * (v * u * v⁻¹ * u⁻¹)⁻¹ ∈ powSub A 2) ∧
    (∀ u ∈ C, ∀ v ∈ C, ∀ w ∈ C,
      (w * (u * v) * w⁻¹ * (u * v)⁻¹) * ((w * u * w⁻¹ * u⁻¹) * (w * v * w⁻¹ * v⁻¹))⁻¹
        ∈ powSub A 2) ∧
    (∀ u ∈ C, ∀ v ∈ C, ∀ w ∈ C,
      ((u * v) * w * (u * v)⁻¹ * w⁻¹) * ((u * w * u⁻¹ * w⁻¹) * (v * w * v⁻¹ * w⁻¹))⁻¹
        ∈ powSub A 2) := by
  have hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  have hAn : A.Normal := hA.normal
  have hunip : ∀ x : P, ∀ y ∈ A, ⁅x, y⁆ ∈ powSub A 2 :=
    fun x y hy => commutator_mem_powSub_two h hA x y hy
  have hA2le : powSub A 2 ≤ A := powSub_le (by norm_num)
  -- the square of an element of `C` lies in `A` (as `C ^ (2) ≤ A`)
  have sq_mem : ∀ x ∈ C, x * x ∈ A := by
    intro x hx
    have h := hC2 (pow_mem_powSub hx)
    rwa [pow_two] at h
  -- the commutator of two elements of `C` lies in `A` (as `⁅C,C⁆ = A`)
  have comm_mem : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ A := by
    intro x hx y hy
    rw [← hCd]
    exact Subgroup.commutator_mem_commutator hx hy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u _ a ha
    exact h8cc_sq_mul_form hAn hab ha
  · intro u _ a ha
    exact h8cc_mem_two hunip ha
  · intro u hu v hv
    exact h8cc_sq_mul_form' hAn hab (sq_mem v hv) (comm_mem v hv u hu)
  · intro u hu v hv
    exact h8cc_mem_four hunip (comm_mem v hv u hu)
  · intro u hu v hv w hw
    exact h8cc_mem_five hab hunip hA2le (comm_mem w hw u hu) (comm_mem w hw v hv)
  · intro u hu v hv w hw
    exact h8cc_mem_six hab hunip hA2le (comm_mem u hu w hw) (comm_mem v hv w hw)

end Work.Higman
