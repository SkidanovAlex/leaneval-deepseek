import Mathlib
import Submission.Work.WilE9.Sharp.Main2
import Submission.Work.WilE9.Sharp.Dom2analysis

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-- The per-order conjunct of `DomSet`/`DomSet2`, as a function of the order list. -/
def Phi (n k : ℕ) (S : List (AEStratum n)) (L : List (Fin n)) : Set (Fin n → ℝ) :=
  projLast (Eset n S L) ∩ projLast (contPart (Eset n S L)) ∩
    (if L.length < k then
      ⋂ i : Fin n, projLast (diffPart (Eset n S L) i ∩ Eset n S (i :: L))
     else Set.univ)

/-- `DomSet` is the interior of the intersection of `Phi` over all order lists. -/
theorem DomSet_eq_iInter (n k : ℕ) (S : List (AEStratum n))
    (G : Set (Fin (n + 1) → ℝ)) :
    DomSet n k S G = interior (projLast (contPart G) ∩ ⋂ L : Ord n k, Phi n k S L.1) := rfl

/-- `DomSet2` is the interior of the intersection of `Phi` over the representatives `repL μ`. -/
theorem DomSet2_eq_iInter (n k : ℕ) (S : List (AEStratum n))
    (G : Set (Fin (n + 1) → ℝ)) :
    DomSet2 n k S G =
      interior (projLast (contPart G) ∩ ⋂ μ : Ord2 n k, Phi n k S (repL μ)) := rfl

/-- The length of `repL μ` is `∑ μ`. -/
theorem length_repL {n k : ℕ} (μ : Ord2 n k) :
    (repL μ).length = ∑ i : Fin n, ((μ.1 i : Fin (k + 1)) : ℕ) := by
  simp only [repL, List.length_flatMap, List.length_replicate]
  rw [← List.sum_toFinset (fun i => ((μ.1 i : Fin (k + 1)) : ℕ)) (List.nodup_finRange n),
    List.toFinset_finRange]

theorem repL_length_le {n k : ℕ} (μ : Ord2 n k) : (repL μ).length ≤ k := by
  rw [length_repL]; exact μ.2

/-- `∑ᵢ count i L = |L|` for a list of elements of `Fin n`. -/
theorem sum_count_eq_length {n : ℕ} (L : List (Fin n)) :
    (∑ i : Fin n, L.count i) = L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hstep : ∀ i : Fin n, (a :: L).count i = L.count i + (if a = i then 1 else 0) := by
      intro i
      simp only [List.count_cons, beq_iff_eq]
    simp only [hstep]
    rw [Finset.sum_add_distrib, ih]
    have : (∑ i : Fin n, (if a = i then (1 : ℕ) else 0)) = 1 := by
      rw [Finset.sum_ite_eq Finset.univ a (fun _ => 1)]
      simp
    rw [this, List.length_cons]

/-- The multi-index whose coordinates are the multiplicities of a list. -/
noncomputable def multOf {n k : ℕ} (L : List (Fin n)) (hL : L.length ≤ k) : Ord2 n k :=
  ⟨fun i => ⟨L.count i, by have := List.count_le_length (a := i) (l := L); omega⟩,
    by
      have h : (∑ i : Fin n,
          ((fun i => (⟨L.count i, by have := List.count_le_length (a := i) (l := L); omega⟩ :
            Fin (k + 1))) i : ℕ)) = L.length := by
        simp only [Fin.val_mk]
        exact sum_count_eq_length L
      omega⟩

/-- `repL (multOf L) ~ L`. -/
theorem perm_repL_multOf {n k : ℕ} (L : List (Fin n)) (hL : L.length ≤ k) :
    L.Perm (repL (multOf L hL)) := by
  rw [List.perm_iff_count]
  intro a
  rw [repL, List.count_flatMap]
  have hcount : ∀ i : Fin n,
      List.count a (List.replicate (L.count i) i) = (if i = a then L.count i else 0) := by
    intro i
    simp only [List.count_replicate, beq_iff_eq]
  have hmap : List.map (List.count a ∘ fun i : Fin n => List.replicate ((multOf L hL).1 i : ℕ) i)
        (List.finRange n)
      = List.map (fun i : Fin n => (if i = a then L.count i else 0)) (List.finRange n) := by
    apply List.map_congr_left
    intro i _
    exact hcount i
  rw [hmap]
  rw [List.sum_map_eq_nsmul_single a (fun i : Fin n => if i = a then L.count i else 0)
    (fun a' h' _ => if_neg h')]
  rw [List.count_finRange]
  simp

/-- `Phi` depends only on the multiset of the order list. -/
theorem Phi_perm {n k : ℕ} {S : List (AEStratum n)}
    (hperm : ∀ (L L' : List (Fin n)), L.length ≤ k → L'.length ≤ k → List.Perm L L' →
      Eset n S L = Eset n S L')
    {L L' : List (Fin n)} (hL : L.length ≤ k) (hL' : L'.length ≤ k) (hp : L.Perm L') :
    Phi n k S L = Phi n k S L' := by
  have hE : Eset n S L = Eset n S L' := hperm L L' hL hL' hp
  have hlen : L.length = L'.length := hp.length_eq
  simp only [Phi]
  rw [hE]
  by_cases h : L.length < k
  · have h' : L'.length < k := by omega
    rw [if_pos h, if_pos h']
    apply le_antisymm
    · intro x hx
      simp only [Set.mem_inter_iff, Set.mem_iInter] at hx ⊢
      refine ⟨hx.1, ?_⟩
      intro i
      have hp' : Eset n S (i :: L) = Eset n S (i :: L') :=
        hperm (i :: L) (i :: L') (by simp [List.length_cons]; omega)
          (by simp [List.length_cons]; omega) (hp.cons i)
      rw [← hp']
      exact hx.2 i
    · intro x hx
      simp only [Set.mem_inter_iff, Set.mem_iInter] at hx ⊢
      refine ⟨hx.1, ?_⟩
      intro i
      have hp' : Eset n S (i :: L) = Eset n S (i :: L') :=
        hperm (i :: L) (i :: L') (by simp [List.length_cons]; omega)
          (by simp [List.length_cons]; omega) (hp.cons i)
      rw [hp']
      exact hx.2 i
  · have h' : ¬ L'.length < k := by omega
    rw [if_neg h, if_neg h']

/-- The intersection over all orders equals the intersection over the multi-index representatives. -/
theorem iInter_Phi_eq {n k : ℕ} {S : List (AEStratum n)}
    (hperm : ∀ (L L' : List (Fin n)), L.length ≤ k → L'.length ≤ k → List.Perm L L' →
      Eset n S L = Eset n S L') :
    (⋂ L : Ord n k, Phi n k S L.1) = (⋂ μ : Ord2 n k, Phi n k S (repL μ)) := by
  apply le_antisymm
  · intro x hx
    simp only [Set.mem_iInter] at hx ⊢
    intro μ
    exact hx ⟨repL μ, repL_length_le μ⟩
  · intro x hx
    simp only [Set.mem_iInter] at hx ⊢
    intro L
    have hp : (repL (multOf L.1 L.2)).Perm L.1 := (perm_repL_multOf L.1 L.2).symm
    have hEq : Phi n k S (repL (multOf L.1 L.2)) = Phi n k S L.1 :=
      Phi_perm hperm (repL_length_le (multOf L.1 L.2)) L.2 hp
    rw [← hEq]
    exact hx (multOf L.1 L.2)

/-- **The multi-index domain equals the list-indexed domain** under order independence. -/
theorem DomSet2_eq_DomSet {n k : ℕ} {S : List (AEStratum n)}
    (hperm : ∀ (L L' : List (Fin n)), L.length ≤ k → L'.length ≤ k → List.Perm L L' →
      Eset n S L = Eset n S L')
    (G : Set (Fin (n + 1) → ℝ)) :
    DomSet2 n k S G = DomSet n k S G := by
  rw [DomSet2_eq_iInter, DomSet_eq_iInter, iInter_Phi_eq hperm]

/-- **The multi-index domain equals the `C^k`-locus.**  `DomSet2` is `DomSet` with the index
`L` replaced by the multi-index representatives `repL μ`; under order independence of `Eset`
(`hperm`) the two intersections agree, so `DomSet2_eq` reduces to `DomSet_eq`. -/
theorem DomSet2_eq {n k : ℕ} {S : List (Work.WilE9.Sharp.AEStratum n)}
    {f : (Fin n → ℝ) → ℝ}
    (hsec : Work.WilE9.Sharp.SecSpec n k S f) (hlim : Work.WilE9.Sharp.LimSpec n k S f)
    (hperm : ∀ (L L' : List (Fin n)), L.length ≤ k → L'.length ≤ k → List.Perm L L' →
      Work.WilE9.Sharp.Eset n S L = Work.WilE9.Sharp.Eset n S L') :
    Work.WilE9.Sharp.DomSet2 n k S (WilkiesDesign.graphOf f) =
      {x : Fin n → ℝ | ContDiffAt ℝ k f x} := by
  rw [DomSet2_eq_DomSet hperm]
  exact DomSet_eq_analysis hsec hlim

end Work.WilE9.Sharp
