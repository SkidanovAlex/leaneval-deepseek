import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Ideal.Operations
import Submission.Work.SSGRoute.prop5.lowerCentralSeriesCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p`-adic weight filtration on the free associative algebra

`A = FreeAssoc X = ℤ[FreeMonoid X]` carries the length ideal `fil X k`.  The Magnus map
`magnus X N : F →* (A ⧸ fil X N)ˣ` sends the descending `p`-central series of `F` into a *weight*
filtration in which a `p`-th power counts as one unit of weight.  The weight-`n` piece `wtz` is
the `ℤ`-span of the elements `p^e · w`, `w` a nonempty word, `|w| + e ≥ n`.

Because `p^e w · p^{e'} w' = p^{e+e'} (ww')` is again a generator, the weight pieces multiply
into each other without any rewriting, and the `l`-th graded component of an element of `wtz n`
is divisible by `p^{n-l}` — this is what makes the `p`-central series argument work.
-/

noncomputable section

open scoped commutatorElement BigOperators

namespace Work.SSGRoute.prop5

variable {X : Type*}

/-- Generators of the weight filtration: `p^e` times a nonempty word `w`, total weight `≥ n`. -/
def wtSet (p : ℕ) (X : Type*) (n : ℕ) : Set (FreeAssoc X) :=
  {a | ∃ (w : FreeMonoid X) (e : ℕ), 1 ≤ w.length ∧ n ≤ w.length + e ∧
        a = MonoidAlgebra.single w ((p : ℤ) ^ e)}

/-- The weight-`n` piece as a `ℤ`-submodule. -/
def wtz (p : ℕ) (X : Type*) (n : ℕ) : Submodule ℤ (FreeAssoc X) := Submodule.span ℤ (wtSet p X n)

theorem mem_wtSet_iff {p n : ℕ} {a : FreeAssoc X} :
    a ∈ wtSet p X n ↔ ∃ (w : FreeMonoid X) (e : ℕ), 1 ≤ w.length ∧ n ≤ w.length + e ∧
        a = MonoidAlgebra.single w ((p : ℤ) ^ e) := Iff.rfl

/-- A weight generator lies in the weight submodule. -/
theorem single_mem_wtz {p n : ℕ} {w : FreeMonoid X} {e : ℕ}
    (hw : 1 ≤ w.length) (hwe : n ≤ w.length + e) :
    MonoidAlgebra.single w ((p : ℤ) ^ e) ∈ wtz p X n :=
  Submodule.subset_span ⟨w, e, hw, hwe, rfl⟩

/-- Products of weight generators are weight generators. -/
theorem single_mul_single_mem_wtz {p n m : ℕ} {w w' : FreeMonoid X} {e e' : ℕ}
    (hw : 1 ≤ w.length) (hwe : n ≤ w.length + e)
    (hw' : 1 ≤ w'.length) (hwe' : m ≤ w'.length + e') :
    MonoidAlgebra.single w ((p : ℤ) ^ e) * MonoidAlgebra.single w' ((p : ℤ) ^ e')
      ∈ wtz p X (n + m) := by
  rw [MonoidAlgebra.single_mul_single, ← pow_add]
  exact single_mem_wtz (by rw [FreeMonoid.length_mul]; omega)
    (by rw [FreeMonoid.length_mul]; omega)

/-- Left multiplication preserves each weight piece. -/
theorem mul_mem_wtz (p : ℕ) (n : ℕ) (c : FreeAssoc X) {x : FreeAssoc X}
    (hx : x ∈ wtz p X n) : c * x ∈ wtz p X n := by
  refine Submodule.span_induction (p := fun x _ => c * x ∈ wtz p X n) ?_ ?_ ?_ ?_ hx
  · rintro a ⟨w, e, hw, hwe, rfl⟩
    rw [← MonoidAlgebra.sum_coeff_single c, Finsupp.sum_mul]
    refine Submodule.sum_mem _ fun v _ => ?_
    simp only
    rw [MonoidAlgebra.single_mul_single]
    have hcfg : MonoidAlgebra.single (v * w) ((c.coeff v) * (p : ℤ) ^ e)
        = (c.coeff v) • MonoidAlgebra.single (v * w) ((p : ℤ) ^ e) := by
      rw [MonoidAlgebra.smul_single']
    rw [hcfg]
    exact Submodule.smul_mem _ _ (single_mem_wtz (by rw [FreeMonoid.length_mul]; omega)
      (by rw [FreeMonoid.length_mul]; omega))
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [mul_add]; exact Submodule.add_mem _ ha hb
  · intro c' a _ ha; rw [mul_smul_comm]; exact Submodule.smul_mem _ c' ha

/-- Right multiplication preserves each weight piece. -/
theorem mul_mem_wtz' (p : ℕ) (n : ℕ) (c : FreeAssoc X) {x : FreeAssoc X}
    (hx : x ∈ wtz p X n) : x * c ∈ wtz p X n := by
  refine Submodule.span_induction (p := fun x _ => x * c ∈ wtz p X n) ?_ ?_ ?_ ?_ hx
  · rintro a ⟨w, e, hw, hwe, rfl⟩
    rw [← MonoidAlgebra.sum_coeff_single c, Finsupp.mul_sum]
    refine Submodule.sum_mem _ fun v _ => ?_
    simp only
    rw [MonoidAlgebra.single_mul_single]
    have hcfg : MonoidAlgebra.single (w * v) ((p : ℤ) ^ e * (c.coeff v))
        = (c.coeff v) • MonoidAlgebra.single (w * v) ((p : ℤ) ^ e) := by
      rw [MonoidAlgebra.smul_single', mul_comm]
    rw [hcfg]
    exact Submodule.smul_mem _ _ (single_mem_wtz (by rw [FreeMonoid.length_mul]; omega)
      (by rw [FreeMonoid.length_mul]; omega))
  · rw [zero_mul]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [add_mul]; exact Submodule.add_mem _ ha hb
  · intro c' a _ ha; rw [smul_mul_assoc]; exact Submodule.smul_mem _ c' ha

/-- The weight piece as an ideal. -/
def wtIdeal (p : ℕ) (X : Type*) (n : ℕ) : Ideal (FreeAssoc X) :=
  { carrier := wtz p X n
    zero_mem' := Submodule.zero_mem _
    add_mem' := fun ha hb => Submodule.add_mem _ ha hb
    smul_mem' := fun c _ hx => by
      show c * _ ∈ wtz p X n
      exact mul_mem_wtz p n c hx }

/-- The product of two weight pieces lands in the weight piece with the sum of the weights. -/
theorem wtIdeal_mul_le (p : ℕ) (X : Type*) (n m : ℕ) :
    wtIdeal p X n * wtIdeal p X m ≤ wtIdeal p X (n + m) := by
  refine Ideal.mul_le.2 fun r hr s hs => ?_
  refine Submodule.span_induction₂ (R := ℤ) (p := fun r s _ _ => r * s ∈ wtz p X (n + m))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hr hs
  · rintro x y ⟨w₁, e₁, hw₁, hwe₁, rfl⟩ ⟨w₂, e₂, hw₂, hwe₂, rfl⟩
    exact single_mul_single_mem_wtz hw₁ hwe₁ hw₂ hwe₂
  · intro y _; rw [zero_mul]; exact Submodule.zero_mem _
  · intro x _; rw [mul_zero]; exact Submodule.zero_mem _
  · intro x y z _ _ _ h₁ h₂; rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
  · intro x y z _ _ _ h₁ h₂; rw [mul_add]; exact Submodule.add_mem _ h₁ h₂
  · intro c x y _ _ h; rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h
  · intro c x y _ _ h; rw [mul_smul_comm]; exact Submodule.smul_mem _ c h

/-- The weight filtration is decreasing. -/
theorem wtIdeal_le (p : ℕ) (X : Type*) {n m : ℕ} (hnm : n ≤ m) :
    wtIdeal p X m ≤ wtIdeal p X n := by
  intro a ha
  change a ∈ wtz p X m at ha
  change a ∈ wtz p X n
  exact Submodule.span_le (R := ℤ).mpr (fun b hb => by
    obtain ⟨w, e, hw, hwe, rfl⟩ := hb
    exact single_mem_wtz hw (le_trans hnm hwe)) ha

/-- `fil k ⊆ wtIdeal k`: the length filtration refines the weight filtration. -/
theorem fil_le_wtIdeal (p : ℕ) (X : Type*) {k : ℕ} (hk : 1 ≤ k) :
    fil X k ≤ wtIdeal p X k := by
  rw [fil]
  refine Ideal.span_le.mpr ?_
  rintro a ⟨w, hw, rfl⟩
  exact single_mem_wtz (e := 0) (le_trans hk hw) (by simpa using hw)


end Work.SSGRoute.prop5
