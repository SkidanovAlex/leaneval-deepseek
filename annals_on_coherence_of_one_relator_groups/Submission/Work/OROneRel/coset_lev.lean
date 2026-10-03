import Mathlib
import Submission.Work.OROneRel.graded_hnn_coset
import Submission.Work.ORBassSerre.Tree.Basic

/-!
# The coset graph of `(H, t)`: infrastructure

The level function on `Coset H t`, the fact that adjacent vertices have levels differing by
exactly one, the translation action on paths, and connectedness.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.OROneRel
namespace GradedHNN

open Quiver

universe u
variable {G : Type u} [Group G] (H : Subgroup G) (t : G) (φbar : G →* Multiplicative ℤ)
  (hH : ∀ h : H, φbar (h : G) = 1)

/-- `(a * b).toAdd = a.toAdd + b.toAdd`. -/
theorem toAdd_mul' (a b : Multiplicative ℤ) : (a * b).toAdd = a.toAdd + b.toAdd := rfl

/-- `(ofAdd n).toAdd = n`. -/
theorem toAdd_ofAdd' (n : ℤ) : (Multiplicative.ofAdd n).toAdd = n := rfl

/-- The level of a coset: the value of `φbar` on any representative. -/
noncomputable def lev (x : Coset H t) : ℤ :=
  Quotient.liftOn' x (fun g => (φbar g).toAdd) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have h1 : φbar (a⁻¹ * b) = 1 := hH ⟨a⁻¹ * b, hab'⟩
    have h2 : φbar (a⁻¹ * b) = (φbar a)⁻¹ * φbar b := by rw [map_mul, map_inv]
    have h3 : φbar a = φbar b := by
      rw [← inv_mul_eq_one, ← h2]; exact h1
    rw [h3])

@[simp] theorem lev_cmk (g : G) : lev H t φbar hH (cmk H t g) = (φbar g).toAdd := rfl

theorem lev_smul (g : G) (x : Coset H t) :
    lev H t φbar hH (g • x) = (φbar g).toAdd + lev H t φbar hH x := by
  induction x using Quotient.inductionOn with
  | h a => rw [smul_cmk, lev_cmk, lev_cmk, map_mul, toAdd_mul']

/-- Adjacent vertices have levels differing by exactly one. -/
theorem lev_adj (ht : φbar t = Multiplicative.ofAdd 1) {x y : Coset H t}
    (h : adjC H t x y) :
    lev H t φbar hH y = lev H t φbar hH x + 1 ∨
      lev H t φbar hH x = lev H t φbar hH y + 1 := by
  obtain ⟨g, h | h⟩ := h
  · refine Or.inl ?_
    rw [h.1, h.2, lev_cmk, lev_cmk, map_mul, ht, toAdd_mul', toAdd_ofAdd']
  · refine Or.inr ?_
    rw [h.1, h.2, lev_cmk, lev_cmk, map_mul, ht, toAdd_mul', toAdd_ofAdd']

/-! ## The action of `G` on paths -/

/-- The translate of an arrow. -/
def smulArrow (g : G) {x y : Coset H t} (e : x ⟶ y) : (g • x) ⟶ (g • y) :=
  ⟨(smul_adjC_iff H t g).mp e.down⟩

/-- The translate of a path. -/
def smulPath (g : G) {x y : Coset H t} (p : Path x y) : Path (g • x) (g • y) :=
  match p with
  | .nil => Path.nil
  | .cons p' e => Path.cons (smulPath g p') (smulArrow H t g e)

@[simp] theorem smulPath_nil (g : G) (x : Coset H t) :
    smulPath H t g (Path.nil : Path x x) = Path.nil := rfl

theorem smulPath_cons (g : G) {x y z : Coset H t} (p : Path x y) (e : y ⟶ z) :
    smulPath H t g (Path.cons p e) = Path.cons (smulPath H t g p) (smulArrow H t g e) := rfl

theorem smulPath_length (g : G) {x y : Coset H t} (p : Path x y) :
    (smulPath H t g p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [smulPath_cons, ih]

/-! ## Connectedness -/

theorem adjC_base_t : adjC H t (baseC H t) (cmk H t t) :=
  ⟨1, Or.inl ⟨rfl, by rw [one_mul]⟩⟩

/-- `a • baseC = cmk a`. -/
theorem smul_baseC (a : G) : a • baseC H t = cmk H t a := by
  show a • cmk H t (1 : G) = cmk H t a
  rw [smul_cmk, mul_one]

/-- The set of group elements whose coset is connected to the base vertex. -/
def connSet : Subgroup G where
  carrier := {g : G | Nonempty (Path (cmk H t g) (baseC H t))}
  one_mem' := ⟨Path.nil⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨pa⟩ := ha
    obtain ⟨pb⟩ := hb
    have hp : Path (a • cmk H t b) (a • baseC H t) := smulPath H t a pb
    rw [smul_cmk, smul_baseC] at hp
    exact ⟨hp.comp pa⟩
  inv_mem' := by
    intro a ha
    obtain ⟨pa⟩ := ha
    have hp : Path (a⁻¹ • cmk H t a) (a⁻¹ • baseC H t) := smulPath H t a⁻¹ pa
    rw [smul_cmk, inv_mul_cancel, smul_baseC] at hp
    exact ⟨hp.reverse⟩

theorem H_le_connSet : H ≤ connSet H t := by
  intro h hh
  have hEq : cmk H t (h : G) = baseC H t := by
    rw [show (h : G) = 1 * (h : G) from (one_mul _).symm]
    exact cmk_mul_mem H t 1 hh
  change Nonempty (Path (cmk H t (h : G)) (baseC H t))
  rw [← hEq]
  exact ⟨Path.nil⟩

theorem t_mem_connSet : t ∈ connSet H t := by
  refine ⟨(Path.cons (Path.nil : Path (baseC H t) (baseC H t)) ⟨?e⟩).reverse⟩
  exact adjC_base_t H t

theorem closure_t_le_connSet : Subgroup.closure ({t} : Set G) ≤ connSet H t :=
  (Subgroup.closure_le _).mpr (by
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact t_mem_connSet H t)

/-- Every vertex is connected to the base vertex. -/
theorem connected_base (hgen : H ⊔ Subgroup.closure ({t} : Set G) = ⊤) (g : G) :
    Nonempty (Path (cmk H t g) (baseC H t)) := by
  have htop : connSet H t = ⊤ := le_antisymm le_top (by
    rw [← hgen]
    exact sup_le (H_le_connSet H t) (closure_t_le_connSet H t))
  have : g ∈ connSet H t := by rw [htop]; trivial
  exact this

/-- The coset graph is connected. -/
theorem connected_coset (hgen : H ⊔ Subgroup.closure ({t} : Set G) = ⊤) (x y : Coset H t) :
    Nonempty (Path x y) := by
  obtain ⟨g, hg⟩ := Quotient.exists_rep x
  obtain ⟨g', hg'⟩ := Quotient.exists_rep y
  obtain ⟨p⟩ := connected_base H t hgen g
  obtain ⟨q⟩ := connected_base H t hgen g'
  rw [← hg, ← hg']
  exact ⟨p.comp q.reverse⟩

/-! ## Loops and the parity of closed paths -/

/-- `t ∉ H`. -/
theorem t_notMem {G : Type u} [Group G] (H : Subgroup G) (t : G)
    (φbar : G →* Multiplicative ℤ)
    (hH : ∀ h : H, φbar (h : G) = 1) (ht : φbar t = Multiplicative.ofAdd 1) :
    t ∉ H := by
  intro htmem
  have h1 : φbar t = 1 := hH ⟨t, htmem⟩
  rw [ht] at h1
  have h2 : (Multiplicative.ofAdd (1 : ℤ)).toAdd = (1 : Multiplicative ℤ).toAdd :=
    congrArg Multiplicative.toAdd h1
  simpa using h2

/-- There are no loops in the coset graph. -/
theorem no_loop {G : Type u} [Group G] (H : Subgroup G) (t : G)
    (φbar : G →* Multiplicative ℤ)
    (hH : ∀ h : H, φbar (h : G) = 1) (ht : φbar t = Multiplicative.ofAdd 1)
    (x : Coset H t) : ¬ adjC H t x x := by
  rintro ⟨g, h | h⟩
  · have heq : cmk H t g = cmk H t (g * t) := by rw [← h.1, h.2]
    have hmem : g⁻¹ * (g * t) ∈ H := (cmk_eq_iff H t).mp heq
    refine t_notMem H t φbar hH ht ?_
    rwa [show g⁻¹ * (g * t) = t from by group] at hmem
  · have heq : cmk H t g = cmk H t (g * t) := by rw [← h.2, h.1]
    have hmem : g⁻¹ * (g * t) ∈ H := (cmk_eq_iff H t).mp heq
    refine t_notMem H t φbar hH ht ?_
    rwa [show g⁻¹ * (g * t) = t from by group] at hmem

/-- For a path, the level difference of the endpoints has the parity of the length. -/
theorem lev_length_parity {G : Type u} [Group G] (H : Subgroup G) (t : G)
    (φbar : G →* Multiplicative ℤ)
    (hH : ∀ h : H, φbar (h : G) = 1) (ht : φbar t = Multiplicative.ofAdd 1)
    {x y : Coset H t} (p : Path x y) :
    ∃ k : ℤ, lev H t φbar hH y - lev H t φbar hH x = 2 * k + p.length := by
  induction p with
  | nil => exact ⟨0, by simp⟩
  | cons p e ih =>
    obtain ⟨k, hk⟩ := ih
    have h1 := lev_adj H t φbar hH ht e.down
    rcases h1 with h1 | h1
    · refine ⟨k, ?_⟩
      simp only [Quiver.Path.length_cons]
      push_cast
      omega
    · refine ⟨k - 1, ?_⟩
      simp only [Quiver.Path.length_cons]
      push_cast
      omega

/-- A closed path has length of the form `2 * k` (`k : ℤ`). -/
theorem closed_length_even {G : Type u} [Group G] (H : Subgroup G) (t : G)
    (φbar : G →* Multiplicative ℤ)
    (hH : ∀ h : H, φbar (h : G) = 1) (ht : φbar t = Multiplicative.ofAdd 1)
    {x : Coset H t} (p : Path x x) : ∃ k : ℤ, (p.length : ℤ) = 2 * k := by
  obtain ⟨k, hk⟩ := lev_length_parity H t φbar hH ht p
  rw [show lev H t φbar hH x - lev H t φbar hH x = 0 from sub_self _] at hk
  exact ⟨-k, by omega⟩

end GradedHNN
end Work.OROneRel
