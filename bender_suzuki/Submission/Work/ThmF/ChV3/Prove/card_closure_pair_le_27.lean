import Mathlib
import Submission.Work.ThmF.ChV3.Prove.pow_swap
import Submission.Work.ThmF.ChV3.Prove.c_cubed
import Submission.Work.ThmF.ChV3.Prove.zpow_emod_eq
import Submission.Work.ThmF.ChV3.Prove.mono_mul
import Submission.Work.ThmF.ChV3.Prove.mono_inv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

/-- The monomial `c^a * u^b * v^d` in a group, with integer exponents. -/
def mo {M : Type*} [Group M] (u v c : M) (a b d : ℤ) : M := c^a * u^b * v^d

/-- The remainder of an integer modulo `3`, as an element of `Fin 3`. -/
def toFin3 (z : ℤ) : Fin 3 :=
  ⟨(z % 3).toNat, by
    rw [Int.toNat_lt (Int.emod_nonneg z (by norm_num : (3:ℤ) ≠ 0))]
    exact Int.emod_lt_of_pos z (by norm_num : (0:ℤ) < 3)⟩

lemma toFin3_intCast (z : ℤ) : (((toFin3 z : Fin 3) : ℕ) : ℤ) = z % 3 := by
  simp only [toFin3, Fin.val_mk]
  exact Int.toNat_of_nonneg (Int.emod_nonneg z (by norm_num : (3:ℤ) ≠ 0))

/--
If `u`, `v` have order dividing `3` and `u * v = c * (v * u)` with `c` commuting with
`u` and `v`, then `⟨u, v⟩` has at most `27` elements (the Heisenberg group of order `27`
over `𝔽₃` is the universal example).
-/
theorem card_closure_pair_le_27 {M : Type*} [Group M] (u v c : M)
    (hu : u ^ 3 = 1) (hv : v ^ 3 = 1) (huv : u * v = c * (v * u))
    (hcu : Commute c u) (hcv : Commute c v) :
    Nat.card ↥(Subgroup.closure ({u, v} : Set M)) ≤ 27 := by
  -- `c ^ 3 = 1`
  have hc3 : c^3 = 1 := c_cubed u v c hu huv hcu
  have hmm := mono_mul u v c huv hcu hcv
  have hmi := mono_inv u v c huv hcu hcv
  -- `S`: all monomials `c^a u^b v^d` with integer exponents. It is closed under
  -- multiplication and inversion, hence contains `⟨u, v⟩`.
  let S : Set M := Set.range (fun p : ℤ × ℤ × ℤ => mo u v c p.1 p.2.1 p.2.2)
  have hS_one : (1 : M) ∈ S := ⟨(0,0,0), by simp [mo]⟩
  have hS_mul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
    rintro x ⟨p, rfl⟩ y ⟨q, rfl⟩
    exact ⟨(p.1 + q.1 - p.2.2 * q.2.1, p.2.1 + q.2.1, p.2.2 + q.2.2),
      (hmm p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2).symm⟩
  have hS_inv : ∀ x ∈ S, x⁻¹ ∈ S := by
    rintro x ⟨p, rfl⟩
    exact ⟨(-p.1 - p.2.2 * p.2.1, -p.2.1, -p.2.2), (hmi p.1 p.2.1 p.2.2).symm⟩
  -- `g`: the same monomials with exponents reduced mod `3`, i.e. indexed by `Fin 3`.
  let g : Fin 3 × Fin 3 × Fin 3 → M := fun p => mo u v c (p.1 : ℤ) (p.2.1 : ℤ) (p.2.2 : ℤ)
  have hS_eq : S = Set.range g := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨(toFin3 p.1, toFin3 p.2.1, toFin3 p.2.2), ?_⟩
      simp only [g, mo, toFin3_intCast]
      rw [← zpow_emod_eq c hc3 p.1, ← zpow_emod_eq u hu p.2.1, ← zpow_emod_eq v hv p.2.2]
    · rintro ⟨p, rfl⟩
      refine ⟨(((p.1 : ℕ) : ℤ), ((p.2.1 : ℕ) : ℤ), ((p.2.2 : ℕ) : ℤ)), ?_⟩
      simp [g, mo]
  -- Every element of `⟨u, v⟩` lies in `S`; the closure induction only needs the
  -- monomial normal form (closed above under multiplication and inversion).
  have hmemS : ∀ x ∈ Subgroup.closure ({u, v} : Set M), x ∈ S := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => x ∈ S) ?_ ?_ ?_ ?_ hx
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨(0,1,0), by simp [mo]⟩
      · exact ⟨(0,0,1), by simp [mo]⟩
    · exact ⟨(0,0,0), by simp [mo]⟩
    · intro x y _ _ hx hy
      exact hS_mul x hx y hy
    · intro x _ hx
      exact hS_inv x hx
  have hmem : ∀ x : ↥(Subgroup.closure ({u, v} : Set M)), (x : M) ∈ Set.range g :=
    fun x => hS_eq ▸ hmemS x x.2
  -- A chosen `Fin 3 × Fin 3 × Fin 3` preimage gives an injection out of `⟨u, v⟩`.
  let f : ↥(Subgroup.closure ({u, v} : Set M)) → Fin 3 × Fin 3 × Fin 3 :=
    fun x => Classical.choose (hmem x)
  have hf : Function.Injective f := by
    intro x y hxy
    simp only [f] at hxy
    have hx : g (Classical.choose (hmem x)) = (x : M) := Classical.choose_spec (hmem x)
    have hy : g (Classical.choose (hmem y)) = (y : M) := Classical.choose_spec (hmem y)
    have : (x : M) = (y : M) := by rw [← hx, ← hy, hxy]
    exact Subtype.ext this
  have hb : Nat.card ↥(Subgroup.closure ({u, v} : Set M)) ≤ Nat.card (Fin 3 × Fin 3 × Fin 3) :=
    Nat.card_le_card_of_injective f hf
  have h27 : Nat.card (Fin 3 × Fin 3 × Fin 3) = 27 := by
    simp
  exact le_trans hb (le_of_eq h27)

end Work.ThmF.ChV3.Prove
