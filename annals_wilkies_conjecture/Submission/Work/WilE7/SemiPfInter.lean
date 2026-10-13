/-
  Area E7: intersection of semi-Pfaffian sets in a *fixed* ambient space.

  A `SemiPf k` set is a DNF of basic sets over one EA chain, intersected with the cube.  The
  union of two such sets is `SemiPf.unionSet` (chains concatenated, DNF appended) -- the two
  sets have *different* fibres, which is why `Star` keeps a list of pieces.  Here we need the
  *intersection*: the two sets live in the same `ℝ^k`, and the intersection is again a DNF over a
  single chain, namely the concatenation `EAChain.cat` together with the *product* of the two DNF
  lists (each basic of one piece conjuncted with each basic of the other).  The evaluation
  lemmas of `SubPfAux.unionSet_set` give the semantics of each side of the concatenated chain.

  `interFam` is the finite family version: the intersection of `n` semi-Pfaffian sets in `ℝ^k`
  (for `n = 0` it is the cube itself, since every `SemiPf.set` is contained in the cube).
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.SubPfAux.unionSet_set
import Submission.Work.WilE7.prodSet

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- Conjunction of two basic sets, over the concatenated chain. -/
def interBasic {k r r' : ℕ} (B : Basic k r) (B' : Basic k r') : Basic k (r + r') :=
  ⟨B.eqs.map EAPoly.inl ++ B'.eqs.map EAPoly.inr,
   B.pos.map EAPoly.inl ++ B'.pos.map EAPoly.inr⟩

theorem interBasic_holds {k r r' : ℕ} (c : EAChain k r) (c' : EAChain k r')
    (B : Basic k r) (B' : Basic k r') (z : Fin k → ℝ) :
    (interBasic B B').holds (EAChain.cat c c') z ↔ B.holds c z ∧ B'.holds c' z := by
  constructor
  · intro h
    refine ⟨⟨fun f hf => ?_, fun f hf => ?_⟩, ⟨fun f hf => ?_, fun f hf => ?_⟩⟩
    · have h1 := h.1 _ (List.mem_append.mpr (Or.inl (List.mem_map_of_mem hf)))
      rwa [SubPfAux.eaEval_cat_inl c c' f z] at h1
    · have h1 := h.2 _ (List.mem_append.mpr (Or.inl (List.mem_map_of_mem hf)))
      rwa [SubPfAux.eaEval_cat_inl c c' f z] at h1
    · have h1 := h.1 _ (List.mem_append.mpr (Or.inr (List.mem_map_of_mem hf)))
      rwa [SubPfAux.eaEval_cat_inr c c' f z] at h1
    · have h1 := h.2 _ (List.mem_append.mpr (Or.inr (List.mem_map_of_mem hf)))
      rwa [SubPfAux.eaEval_cat_inr c c' f z] at h1
  · rintro ⟨h, h'⟩
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · rcases List.mem_append.mp hf with hf | hf
      · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
        rw [SubPfAux.eaEval_cat_inl]; exact h.1 f₀ hf₀
      · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
        rw [SubPfAux.eaEval_cat_inr]; exact h'.1 f₀ hf₀
    · rcases List.mem_append.mp hf with hf | hf
      · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
        rw [SubPfAux.eaEval_cat_inl]; exact h.2 f₀ hf₀
      · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
        rw [SubPfAux.eaEval_cat_inr]; exact h'.2 f₀ hf₀

/-- Intersection of two semi-Pfaffian sets in the same ambient space. -/
def interSet {k : ℕ} (X Y : SemiPf k) : SemiPf k :=
  ⟨X.r + Y.r, EAChain.cat X.c Y.c,
   (X.basics.product Y.basics).map (fun b => interBasic b.1 b.2)⟩

theorem interSet_set {k : ℕ} (X Y : SemiPf k) : (interSet X Y).set = X.set ∩ Y.set := by
  have hkey : ∀ z : Fin k → ℝ,
      (∃ B ∈ (X.basics.product Y.basics).map (fun b => interBasic b.1 b.2),
        B.holds (EAChain.cat X.c Y.c) z) ↔
      (∃ B ∈ X.basics, B.holds X.c z) ∧ (∃ B ∈ Y.basics, B.holds Y.c z) := by
    intro z
    rw [exists_mem_product_map]
    constructor
    · rintro ⟨a, ha, b, hb, h⟩
      rw [interBasic_holds] at h
      exact ⟨⟨a, ha, h.1⟩, ⟨b, hb, h.2⟩⟩
    · rintro ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
      exact ⟨a, ha, b, hb, (interBasic_holds X.c Y.c a b z).mpr ⟨h1, h2⟩⟩
  ext z
  simp only [SemiPf.set, Set.mem_ofPred_eq, Set.mem_inter_iff, interSet]
  constructor
  · rintro ⟨hz, B, hB, hBh⟩
    obtain ⟨h1, h2⟩ := (hkey z).mp ⟨B, hB, hBh⟩
    exact ⟨⟨hz, h1⟩, ⟨hz, h2⟩⟩
  · rintro ⟨⟨hz, h1⟩, ⟨-, h2⟩⟩
    exact ⟨hz, (hkey z).mpr ⟨h1, h2⟩⟩

/-- The trivial piece: the whole cube, as a `SemiPf` set. -/
def topSemiPf (k : ℕ) : SemiPf k := ⟨0, EAChain.nil k, [⟨[], []⟩]⟩

theorem topSemiPf_set (k : ℕ) : (topSemiPf k).set = cubeC k := by
  ext z
  constructor
  · rintro ⟨hz, -, -, -⟩
    exact hz
  · intro hz
    exact ⟨hz, ⟨[], []⟩, List.mem_singleton.mpr rfl, ⟨fun f hf => by simp at hf,
      fun f hf => by simp at hf⟩⟩

/-- Intersection of a finite family of semi-Pfaffian sets in the same ambient space. -/
def interFam {k : ℕ} : (n : ℕ) → (Fin n → SemiPf k) → SemiPf k
  | 0, _ => topSemiPf k
  | n + 1, X => interSet (X (Fin.last n)) (interFam n (fun i => X (Fin.castSucc i)))

theorem mem_interFam {k : ℕ} (n : ℕ) (X : Fin n → SemiPf k) (z : Fin k → ℝ) :
    z ∈ (interFam n X).set ↔ z ∈ cubeC k ∧ ∀ i : Fin n, z ∈ (X i).set := by
  induction n with
  | zero =>
    rw [interFam, topSemiPf_set]
    exact ⟨fun h => ⟨h, fun i => i.elim0⟩, fun h => h.1⟩
  | succ n ih =>
    rw [interFam, interSet_set, Set.mem_inter_iff, ih]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h2, fun i => ?_⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact h1
      · exact h3 j
    · rintro ⟨h2, h4⟩
      exact ⟨h4 (Fin.last n), h2, fun j => h4 (Fin.castSucc j)⟩

end Work.WilE7
