import Mathlib.GroupTheory.GroupAction.Ring
import Submission.Commons.Algebra.Lie.PBW.standardMonomial_spanning
import Submission.Commons.LinearAlgebra.TensorAlgebra.word_eq_basis
import Submission.Commons.Algebra.Lie.UniversalEnveloping.linearMap_quotient_factor
import Submission.Commons.LinearAlgebra.Basis.subtype_linearIndependent

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
universe u v w

namespace Commons.Algebra.Lie.PBW

variable {K L ι : Type u} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [LinearOrder ι]

/-- basis vector of a word in the tensor algebra -/
def wordBasis (e : Module.Basis ι K L) (w : List ι) : TensorAlgebra K L := e.tensorAlgebra w

section FirstDescent
open List
variable {ι : Type u} [LinearOrder ι]
def firstDesc : List ι → Option (List ι × ι × ι × List ι)
  | [] => none
  | [_] => none
  | a :: b :: t => if b < a then some ([], a, b, t) else
      match firstDesc (b :: t) with
      | none => none
      | some (u, x, y, v) => some (a :: u, x, y, v)

lemma pbwspan_sorted_of_firstDesc_none : ∀ w : List ι, firstDesc w = none → pbwspan_sorted w
  | [], _ => by simp [pbwspan_sorted]
  | [_], _ => by simp [pbwspan_sorted]
  | a :: b :: t, h => by
      have hbn : ¬ b < a := by
        intro hba
        simp [firstDesc, hba] at h
      have hab : a ≤ b := le_of_not_gt hbn
      have hfd' : firstDesc (b :: t) = none := by
        by_cases h1 : firstDesc (b :: t) = none
        · exact h1
        · cases hd : firstDesc (b :: t) with
          | none => exact False.elim (h1 hd)
          | some d =>
              rcases d with ⟨u, x, y, v⟩
              simp [firstDesc, hbn, hd] at h
      have hsb : pbwspan_sorted (b :: t) := pbwspan_sorted_of_firstDesc_none (b :: t) hfd'
      rw [pbwspan_sorted]
      rw [pairwise_cons]
      constructor
      · intro c hc
        rw [mem_cons] at hc
        rcases hc with rfl | hc
        · exact hab
        · exact le_trans hab (List.rel_of_pairwise_cons hsb (by simp [hc]))
      · exact hsb

def firstDescData : (w : List ι) → (h : firstDesc w ≠ none) →
    {d : List ι × ι × ι × List ι // w = d.1 ++ d.2.1 :: d.2.2.1 :: d.2.2.2 ∧
      d.2.2.1 < d.2.1 ∧ pbwspan_sorted d.1 ∧ ∀ z ∈ d.1, z ≤ d.2.1}
  | [], h => by simp [firstDesc] at h
  | [_], h => by simp [firstDesc] at h
  | a :: b :: t, h => by
      classical
      by_cases hba : b < a
      · exact ⟨([], a, b, t), rfl, hba, by simp [pbwspan_sorted], by intro z hz; simpa using hz⟩
      · have hab : a ≤ b := le_of_not_gt hba
        have h1 : firstDesc (b :: t) ≠ none := by
          intro hn
          simp [firstDesc, hba, hn] at h
        rcases firstDescData (b :: t) h1 with ⟨d, hw, hxy, hsu, hux⟩
        refine ⟨(a :: d.1, d.2.1, d.2.2.1, d.2.2.2), ?_, hxy, ?_, ?_⟩
        · rw [hw]; simp
        · rw [pbwspan_sorted]
          rw [List.pairwise_cons]
          constructor
          · intro z hz
            by_cases hu : d.1 = []
            · simpa [hu] using hz
            · rcases List.exists_cons_of_ne_nil hu with ⟨c, u1, hu_eq⟩
              have he : b = c := by
                have hw' : b :: t = c :: (u1 ++ d.2.1 :: d.2.2.1 :: d.2.2.2) := by
                  simpa [hu_eq, List.append_assoc] using hw
                exact List.cons.inj hw' |>.1
              have hz' : z ∈ c :: u1 := by
                rw [← hu_eq]
                exact hz
              rw [List.mem_cons] at hz'
              rcases hz' with rfl | hz'
              · exact le_trans hab (le_of_eq he)
              · have hsu' : pbwspan_sorted (c :: u1) := by simpa [hu_eq] using hsu
                exact le_trans hab (le_trans (le_of_eq he) (List.rel_of_pairwise_cons hsu' hz'))
          · exact hsu
        · intro z hz
          rw [List.mem_cons] at hz
          rcases hz with rfl | hz
          · by_cases hu : d.1 = []
            · have hx : d.2.1 = b := by
                have hw' : b :: t = d.2.1 :: d.2.2.1 :: d.2.2.2 := by simpa [hu] using hw
                exact (List.cons.inj hw' |>.1).symm
              rw [hx]
              exact hab
            · rcases List.exists_cons_of_ne_nil hu with ⟨c, u1, hu_eq⟩
              have he : b = c := by
                have hw' : b :: t = c :: (u1 ++ d.2.1 :: d.2.2.1 :: d.2.2.2) := by
                  simpa [hu_eq, List.append_assoc] using hw
                exact List.cons.inj hw' |>.1
              have hbcx : b ≤ d.2.1 := hux b (by rw [hu_eq]; simp [he])
              exact le_trans hab hbcx
          · exact hux z hz

end FirstDescent

section Sigma

variable (e : Module.Basis ι K L)

/-- `pbwspan_Rel` is invariant under replacing a word by an equal word -/
lemma Rel_cast {w w0 s : List ι} (h : w = w0) (hs : pbwspan_Rel s w0) : pbwspan_Rel s w := by
  simpa [h] using hs

/-- one recursion step of the straightening map -/
noncomputable def sWordF (w : List ι) (ih : ∀ y : List ι, pbwspan_Rel y w → TensorAlgebra K L) :
    TensorAlgebra K L := by
  by_cases hs : pbwspan_sorted w
  · exact wordBasis e w
  · have hfd : firstDesc w ≠ none := by
      intro hn
      exact hs (pbwspan_sorted_of_firstDesc_none w hn)
    let D := firstDescData w hfd
    exact ih (D.1.1 ++ D.1.2.2.1 :: D.1.2.1 :: D.1.2.2.2)
          (Rel_cast D.2.1 (pbwspan_Rel_swap D.1.2.1 D.1.2.2.1 D.2.2.1 D.1.1 D.1.2.2.2)) +
      (e.repr ⁅e D.1.2.1, e D.1.2.2.1⁆).sum (fun k dk =>
        dk • ih (D.1.1 ++ k :: D.1.2.2.2)
          (Rel_cast D.2.1 (pbwspan_Rel_of_len_lt (pbwspan_len_delete D.1.1 D.1.2.2.2 k D.1.2.1 D.1.2.2.1))))

/-- Values of the straightening map on words, reducing at the first descent. -/
noncomputable def sWord : List ι → TensorAlgebra K L := pbwspan_wfRel.fix (sWordF e)

/-- recursion equation of the straightening map -/
lemma sWord_fix (w : List ι) :
    sWord e w = sWordF e w (fun y _ => sWord e y) := by
  unfold sWord
  rw [WellFounded.fix_eq]

/-- The linear straightening map on the tensor algebra. -/
noncomputable def sigmaLin : TensorAlgebra K L →ₗ[K] TensorAlgebra K L :=
  ((e.tensorAlgebra.constr K) (sWord e))

/-- The straightening map equals the identity on sorted words. -/
lemma sWord_sorted (w : List ι) (hs : pbwspan_sorted w) : sWord e w = wordBasis e w := by
  rw [sWord_fix]
  simp [sWordF, hs]

/-- a word containing a strict descent `x :: y` (y < x) is not sorted -/
lemma not_sorted_of_desc_concat {u v : List ι} {x y : ι} (hxy : y < x) :
    ¬ pbwspan_sorted (u ++ x :: y :: v) := by
  intro hs
  have hle : x ≤ y := by
    induction u with
    | nil =>
        exact List.rel_of_pairwise_cons (R := fun a b : ι => a ≤ b) hs (by simp)
    | cons a t ih =>
        have htail : pbwspan_sorted (t ++ x :: y :: v) := by
          simpa [pbwspan_sorted] using (List.pairwise_cons.mp hs).2
        exact ih htail
  exact not_lt_of_ge hle hxy

/-- canonical first-descent data for a non-sorted word -/
noncomputable def fdd (w : List ι) (hs : ¬ pbwspan_sorted w) :=
  firstDescData w (by intro hn; exact hs (pbwspan_sorted_of_firstDesc_none w hn))

/-- expansion of the straightening map at the first descent -/
lemma sWord_expand (w : List ι) (hs : ¬ pbwspan_sorted w) :
    sWord e w = sWord e ((fdd w hs).1.1 ++ (fdd w hs).1.2.2.1 :: (fdd w hs).1.2.1 :: (fdd w hs).1.2.2.2) +
      (e.repr ⁅e (fdd w hs).1.2.1, e (fdd w hs).1.2.2.1⁆).sum
        (fun k c => c • sWord e ((fdd w hs).1.1 ++ k :: (fdd w hs).1.2.2.2)) := by
  rw [sWord_fix]
  unfold sWordF
  dsimp
  simp [fdd, hs]

/-- left cancellation for list concatenation -/
lemma append_left_cancel' {α : Type u} : ∀ (u a b : List α), u ++ a = u ++ b → a = b
  | [], a, b, h => h
  | x :: u, a, b, h => append_left_cancel' u a b (List.cons.inj h).2

/-- in a sorted list `u ++ x :: t'`, the element `x` is ≤ every element of `t'` -/
lemma le_of_mem_sorted_after {u t' : List ι} {x z : ι}
    (hs : pbwspan_sorted (u ++ x :: t')) (hz : z ∈ t') : x ≤ z := by
  induction u with
  | nil =>
      exact List.rel_of_pairwise_cons (R := fun a b : ι => a ≤ b) hs hz
  | cons a u' ih =>
      have htail : pbwspan_sorted (u' ++ x :: t') := by
        simpa [pbwspan_sorted] using (List.pairwise_cons.mp hs).2
      exact ih htail

/-- two prefixes of the same list are comparable -/
lemma prefix_comparable {α : Type u} (u R U0 S : List α) (h : u ++ R = U0 ++ S) :
    (∃ t : List α, U0 = u ++ t) ∨ (∃ t : List α, u = U0 ++ t) := by
  induction u generalizing U0 with
  | nil => exact Or.inl ⟨U0, by simp⟩
  | cons a u' ih =>
      cases U0 with
      | nil => exact Or.inr ⟨a :: u', by simp⟩
      | cons b U0' =>
          have hh := List.cons.inj h
          have hab : a = b := hh.1
          have hrest : u' ++ R = U0' ++ S := hh.2
          rcases ih (U0 := U0') hrest with ⟨t, hU⟩ | ⟨t, hu⟩
          · left
            refine ⟨t, ?_⟩
            rw [← hab, hU]
            rfl
          · right
            refine ⟨t, ?_⟩
            rw [← hab, hu]
            rfl

/-- The disjoint-descent confluence identity (both descents separated): reduces by the induction
hypothesis to a pure Fubini/commutativity identity. -/
lemma finset_sum_smul_comm (sα sβ : Finset ι) (a b : ι → K) (x : ι → ι → TensorAlgebra K L) :
    sα.sum (fun i => a i • sβ.sum (fun j => b j • x i j)) =
      sβ.sum (fun j => b j • sα.sum (fun i => a i • x i j)) := by
  calc
    sα.sum (fun i => a i • sβ.sum (fun j => b j • x i j))
        = sα.sum (fun i => sβ.sum (fun j => (a i * b j) • x i j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [smul_smul]
    _ = sβ.sum (fun j => sα.sum (fun i => (a i * b j) • x i j)) := by
          rw [Finset.sum_comm]
    _ = sβ.sum (fun j => b j • sα.sum (fun i => a i • x i j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [mul_comm]
          rw [← smul_smul]

lemma finsupp_smul_add (f : ι →₀ K) (g h : ι → TensorAlgebra K L) :
    f.sum (fun k c => c • (g k + h k)) = f.sum (fun k c => c • g k) + f.sum (fun k c => c • h k) := by
  calc
    f.sum (fun k c => c • (g k + h k))
        = f.support.sum (fun a => f a • (g a + h a)) := rfl
    _ = f.support.sum (fun a => f a • g a + f a • h a) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [smul_add]
    _ = f.support.sum (fun a => f a • g a) + f.support.sum (fun a => f a • h a) := by
          rw [Finset.sum_add_distrib]

lemma finsupp_sum_smul_comm (f g : ι →₀ K) (x : ι → ι → TensorAlgebra K L) :
    f.sum (fun k c => c • g.sum (fun j d => d • x k j)) =
      g.sum (fun j d => d • f.sum (fun k c => c • x k j)) := by
  dsimp [Finsupp.sum]
  exact finset_sum_smul_comm f.support g.support (fun i => f i) (fun j => g j) x

lemma sWord_disjoint_case (U0 t2 v : List ι) (x y x0 y0 : ι)
    (hy0x0 : y0 < x0) (hxy : y < x)
    (hInd : ∀ w' : List ι, pbwspan_Rel w' (U0 ++ x0 :: y0 :: t2 ++ x :: y :: v) →
       ∀ (u v : List ι) (a b : ι), b < a → w' = u ++ a :: b :: v →
          sWord e w' = sWord e (u ++ b :: a :: v) +
            (e.repr ⁅e a, e b⁆).sum (fun k d => d • sWord e (u ++ k :: v))) :
    sWord e (U0 ++ y0 :: x0 :: t2 ++ x :: y :: v) +
        (e.repr ⁅e x0, e y0⁆).sum (fun k d => d • sWord e (U0 ++ k :: t2 ++ x :: y :: v)) =
      sWord e (U0 ++ x0 :: y0 :: t2 ++ y :: x :: v) +
        (e.repr ⁅e x, e y⁆).sum (fun k d => d • sWord e (U0 ++ x0 :: y0 :: t2 ++ k :: v)) := by
  classical
  have hRelW : ∀ w' : List ι, pbwspan_Rel w' (U0 ++ x0 :: y0 :: t2 ++ x :: y :: v) → Prop := by
    intro w' h
    exact True
  -- (1) σ(U0 ++ y0 :: x0 :: t2 ++ x :: y :: v) = σ(E') + Σ c(k) σ(Gk)   (target swap inside the swapped word)
  have h1 : sWord e (U0 ++ y0 :: x0 :: t2 ++ x :: y :: v) =
      sWord e (U0 ++ y0 :: x0 :: t2 ++ y :: x :: v) +
        (e.repr ⁅e x, e y⁆).sum
          (fun k d => d • sWord e (U0 ++ y0 :: x0 :: t2 ++ k :: v)) := by
    have hRel : pbwspan_Rel (U0 ++ y0 :: x0 :: t2 ++ x :: y :: v)
        (U0 ++ x0 :: y0 :: t2 ++ x :: y :: v) := by
      simpa [List.append_assoc] using
        (pbwspan_Rel_swap x0 y0 hy0x0 U0 (t2 ++ x :: y :: v))
    simpa [List.append_assoc] using
      (hInd (U0 ++ y0 :: x0 :: t2 ++ x :: y :: v) hRel (U0 ++ y0 :: x0 :: t2) v x y hxy
        (by simp [List.append_assoc]))
  -- (2) σ(U0 ++ k0 :: t2 ++ x :: y :: v) = σ(U0 ++ k0 :: t2 ++ y :: x :: v) + Σ c(k) σ(...)
  have h2 : ∀ k0 : ι,
      sWord e (U0 ++ k0 :: t2 ++ x :: y :: v) =
        sWord e (U0 ++ k0 :: t2 ++ y :: x :: v) +
          (e.repr ⁅e x, e y⁆).sum (fun k d => d • sWord e (U0 ++ k0 :: t2 ++ k :: v)) := by
    intro k0
    have hRel : pbwspan_Rel (U0 ++ k0 :: t2 ++ x :: y :: v)
        (U0 ++ x0 :: y0 :: t2 ++ x :: y :: v) := by
      exact pbwspan_Rel_of_len_lt (by
        simp [List.length_append])
    simpa [List.append_assoc] using
      (hInd (U0 ++ k0 :: t2 ++ x :: y :: v) hRel (U0 ++ k0 :: t2) v x y hxy rfl)
  -- (3) σ(B) = σ(E') + Σ c0(k0) σ(U0 ++ k0 :: t2 ++ y :: x :: v)
  have h3 : sWord e (U0 ++ x0 :: y0 :: t2 ++ y :: x :: v) =
      sWord e (U0 ++ y0 :: x0 :: t2 ++ y :: x :: v) +
        (e.repr ⁅e x0, e y0⁆).sum
          (fun k0 d0 => d0 • sWord e (U0 ++ k0 :: t2 ++ y :: x :: v)) := by
    have hRel : pbwspan_Rel (U0 ++ x0 :: y0 :: t2 ++ y :: x :: v)
        (U0 ++ x0 :: y0 :: t2 ++ x :: y :: v) := by
      simpa [List.append_assoc] using
        (pbwspan_Rel_swap x y hxy (U0 ++ x0 :: y0 :: t2) v)
    simpa [List.append_assoc] using
      (hInd (U0 ++ x0 :: y0 :: t2 ++ y :: x :: v) hRel U0 (t2 ++ y :: x :: v) x0 y0 hy0x0
        (by simp [List.append_assoc]))
  -- (4) σ(Dk) = σ(Gk) + Σ c0(k0) σ(Hk0k)
  have h4 : ∀ k : ι,
      sWord e (U0 ++ x0 :: y0 :: t2 ++ k :: v) =
        sWord e (U0 ++ y0 :: x0 :: t2 ++ k :: v) +
          (e.repr ⁅e x0, e y0⁆).sum
            (fun k0 d0 => d0 • sWord e (U0 ++ k0 :: t2 ++ k :: v)) := by
    intro k
    have hRel : pbwspan_Rel (U0 ++ x0 :: y0 :: t2 ++ k :: v)
        (U0 ++ x0 :: y0 :: t2 ++ x :: y :: v) := by
      exact pbwspan_Rel_of_len_lt (by
        simp [List.length_append])
    simpa [List.append_assoc] using
      (hInd (U0 ++ x0 :: y0 :: t2 ++ k :: v) hRel U0 (t2 ++ k :: v) x0 y0 hy0x0
        (by simp [List.append_assoc]))

  let c0 : ι →₀ K := e.repr ⁅e x0, e y0⁆
  let c : ι →₀ K := e.repr ⁅e x, e y⁆
  have h2sum : c0.sum (fun k0 d0 => d0 • sWord e (U0 ++ k0 :: t2 ++ x :: y :: v)) =
      c0.sum (fun k0 d0 => d0 • (sWord e (U0 ++ k0 :: t2 ++ y :: x :: v) +
        c.sum (fun k d => d • sWord e (U0 ++ k0 :: t2 ++ k :: v)))) := by
    apply Finsupp.sum_congr
    intro k0 hk0
    rw [h2 k0]
  have h4sum : c.sum (fun k d => d • sWord e (U0 ++ x0 :: y0 :: t2 ++ k :: v)) =
      c.sum (fun k d => d • (sWord e (U0 ++ y0 :: x0 :: t2 ++ k :: v) +
        c0.sum (fun k0 d0 => d0 • sWord e (U0 ++ k0 :: t2 ++ k :: v)))) := by
    apply Finsupp.sum_congr
    intro k hk
    rw [h4 k]
  have hswap : c0.sum (fun k0 d0 => d0 • c.sum (fun k d => d • sWord e (U0 ++ k0 :: t2 ++ k :: v))) =
      c.sum (fun k d => d • c0.sum (fun k0 d0 => d0 • sWord e (U0 ++ k0 :: t2 ++ k :: v))) := by
    exact finsupp_sum_smul_comm c0 c (fun k0 k => sWord e (U0 ++ k0 :: t2 ++ k :: v))
  have c0sum_split :
      c0.sum (fun k0 d0 => d0 • (sWord e (U0 ++ k0 :: t2 ++ y :: x :: v) +
        c.sum (fun k d => d • sWord e (U0 ++ k0 :: t2 ++ k :: v)))) =
        c0.sum (fun k0 d0 => d0 • sWord e (U0 ++ k0 :: t2 ++ y :: x :: v)) +
          c0.sum (fun k0 d0 => d0 • c.sum (fun k d => d • sWord e (U0 ++ k0 :: t2 ++ k :: v))) := by
    exact finsupp_smul_add c0 (fun k0 => sWord e (U0 ++ k0 :: t2 ++ y :: x :: v))
      (fun k0 => c.sum (fun k d => d • sWord e (U0 ++ k0 :: t2 ++ k :: v)))
  have cd :
      c.sum (fun k d => d • (sWord e (U0 ++ y0 :: x0 :: t2 ++ k :: v) +
        c0.sum (fun k0 d0 => d0 • sWord e (U0 ++ k0 :: t2 ++ k :: v)))) =
        c.sum (fun k d => d • sWord e (U0 ++ y0 :: x0 :: t2 ++ k :: v)) +
          c.sum (fun k d => d • c0.sum (fun k0 d0 => d0 • sWord e (U0 ++ k0 :: t2 ++ k :: v))) := by
    exact finsupp_smul_add c (fun k => sWord e (U0 ++ y0 :: x0 :: t2 ++ k :: v))
      (fun k => c0.sum (fun k0 d0 => d0 • sWord e (U0 ++ k0 :: t2 ++ k :: v)))
  calc
    sWord e (U0 ++ y0 :: x0 :: t2 ++ x :: y :: v) +
        c0.sum (fun k0 d0 => d0 • sWord e (U0 ++ k0 :: t2 ++ x :: y :: v))
        = (sWord e (U0 ++ y0 :: x0 :: t2 ++ y :: x :: v) +
            c.sum (fun k d => d • sWord e (U0 ++ y0 :: x0 :: t2 ++ k :: v))) +
          c0.sum (fun k0 d0 => d0 • sWord e (U0 ++ k0 :: t2 ++ x :: y :: v)) := by
            rw [h1]
    _ = (sWord e (U0 ++ y0 :: x0 :: t2 ++ y :: x :: v) +
          c.sum (fun k d => d • sWord e (U0 ++ y0 :: x0 :: t2 ++ k :: v))) +
        c0.sum (fun k0 d0 => d0 • (sWord e (U0 ++ k0 :: t2 ++ y :: x :: v) +
          c.sum (fun k d => d • sWord e (U0 ++ k0 :: t2 ++ k :: v)))) := by
            rw [h2sum]
    _ = (sWord e (U0 ++ y0 :: x0 :: t2 ++ y :: x :: v) +
          c.sum (fun k d => d • sWord e (U0 ++ y0 :: x0 :: t2 ++ k :: v))) +
        (c0.sum (fun k0 d0 => d0 • sWord e (U0 ++ k0 :: t2 ++ y :: x :: v)) +
          c0.sum (fun k0 d0 => d0 • c.sum (fun k d => d • sWord e (U0 ++ k0 :: t2 ++ k :: v)))) := by
            rw [c0sum_split]
    _ = (sWord e (U0 ++ y0 :: x0 :: t2 ++ y :: x :: v) +
          c.sum (fun k d => d • sWord e (U0 ++ y0 :: x0 :: t2 ++ k :: v))) +
        (c0.sum (fun k0 d0 => d0 • sWord e (U0 ++ k0 :: t2 ++ y :: x :: v)) +
          c.sum (fun k d => d • c0.sum (fun k0 d0 => d0 • sWord e (U0 ++ k0 :: t2 ++ k :: v)))) := by
            rw [hswap]
    _ = (sWord e (U0 ++ y0 :: x0 :: t2 ++ y :: x :: v) +
          c0.sum (fun k0 d0 => d0 • sWord e (U0 ++ k0 :: t2 ++ y :: x :: v))) +
        (c.sum (fun k d => d • sWord e (U0 ++ y0 :: x0 :: t2 ++ k :: v)) +
          c.sum (fun k d => d • c0.sum (fun k0 d0 => d0 • sWord e (U0 ++ k0 :: t2 ++ k :: v)))) := by
            ac_rfl
    _ = sWord e (U0 ++ x0 :: y0 :: t2 ++ y :: x :: v) +
        (c.sum (fun k d => d • sWord e (U0 ++ y0 :: x0 :: t2 ++ k :: v)) +
          c.sum (fun k d => d • c0.sum (fun k0 d0 => d0 • sWord e (U0 ++ k0 :: t2 ++ k :: v)))) := by
            rw [← h3]
    _ = sWord e (U0 ++ x0 :: y0 :: t2 ++ y :: x :: v) +
          c.sum (fun k d => d • (sWord e (U0 ++ y0 :: x0 :: t2 ++ k :: v) +
            c0.sum (fun k0 d0 => d0 • sWord e (U0 ++ k0 :: t2 ++ k :: v)))) := by
            rw [← cd]
    _ = sWord e (U0 ++ x0 :: y0 :: t2 ++ y :: x :: v) +
          c.sum (fun k d => d • sWord e (U0 ++ x0 :: y0 :: t2 ++ k :: v)) := by
            rw [h4sum]

/-- Cyclic Jacobi identity (inner form). -/
lemma lie_cyclic_jacobi (x y z : L) : ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 := by
  have hcancel : ⁅y, ⁅x, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ = 0 := by
    have hs : ⁅x, z⁆ + ⁅z, x⁆ = 0 := by
      have hs' : ⁅z, x⁆ = -⁅x, z⁆ := (lie_skew z x).symm
      exact (congrArg (fun t : L => ⁅x, z⁆ + t) hs').trans (add_neg_cancel (⁅x, z⁆))
    have hly : ⁅y, ⁅x, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ = ⁅y, ⁅x, z⁆ + ⁅z, x⁆⁆ := by
      rw [← lie_add y]
    exact hly.trans (by rw [hs]; simp)
  calc
    ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆
        = (⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆) + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ := by rw [LieRing.leibniz_lie x y z]
    _ = ⁅⁅x, y⁆, z⁆ + ⁅z, ⁅x, y⁆⁆ := by
          rw [add_assoc (⁅⁅x, y⁆, z⁆) (⁅y, ⁅x, z⁆⁆) (⁅y, ⁅z, x⁆⁆)]
          rw [add_assoc (⁅⁅x, y⁆, z⁆) (⁅y, ⁅x, z⁆⁆ + ⁅y, ⁅z, x⁆⁆) (⁅z, ⁅x, y⁆⁆)]
          rw [hcancel]
          simp
    _ = 0 := by
          have hz : ⁅z, ⁅x, y⁆⁆ = -⁅⁅x, y⁆, z⁆ := (lie_skew z ⁅x, y⁆).symm
          exact (congrArg (fun t : L => ⁅⁅x, y⁆, z⁆ + t) hz).trans (add_neg_cancel (⁅⁅x, y⁆, z⁆))

/-- Cyclic Jacobi identity (outer form): `[[x,y],z] + [[y,z],x] + [[z,x],y] = 0`. -/
lemma lie_cyclic_jacobi_outer (x y z : L) : ⁅⁅x, y⁆, z⁆ + ⁅⁅y, z⁆, x⁆ + ⁅⁅z, x⁆, y⁆ = 0 := by
  have hin := lie_cyclic_jacobi y z x
  -- hin : [y,[z,x]] + [z,[x,y]] + [x,[y,z]] = 0 ; each inner bracket = -(outer) by skew
  have hs1 : ⁅y, ⁅z, x⁆⁆ = -⁅⁅z, x⁆, y⁆ := (lie_skew y ⁅z, x⁆).symm
  have hs2 : ⁅z, ⁅x, y⁆⁆ = -⁅⁅x, y⁆, z⁆ := (lie_skew z ⁅x, y⁆).symm
  have hs3 : ⁅x, ⁅y, z⁆⁆ = -⁅⁅y, z⁆, x⁆ := (lie_skew x ⁅y, z⁆).symm
  have hin' : -⁅⁅z, x⁆, y⁆ + (-⁅⁅x, y⁆, z⁆ + -⁅⁅y, z⁆, x⁆) = 0 := by
    rw [hs1, hs2, hs3] at hin
    rw [add_assoc] at hin
    exact hin
  -- now -S = 0 so S = 0
  have hneg : -(⁅⁅x, y⁆, z⁆ + ⁅⁅y, z⁆, x⁆ + ⁅⁅z, x⁆, y⁆) = 0 := by
    simpa [add_comm, add_left_comm, add_assoc] using hin'
  exact neg_eq_zero.mp hneg

/-- Coefficient form of the outer cyclic Jacobi identity. -/
lemma bracketJacobi_coeff_outer (e : Module.Basis ι K L) (a b c m : ι) :
    (e.repr ⁅⁅e a, e b⁆, e c⁆) m + (e.repr ⁅⁅e b, e c⁆, e a⁆) m + (e.repr ⁅⁅e c, e a⁆, e b⁆) m = 0 := by
  have h := lie_cyclic_jacobi_outer (e a) (e b) (e c)
  have hr := congrArg (fun v : L => e.repr v m) h
  simpa [add_assoc] using hr

/-- Negation commutes with `Finsupp.sum` (linear in the coefficient). -/
lemma finsupp_sum_neg {M : Type u} [AddCommGroup M] [Module K M] (f : ι →₀ K) (x : ι → M) :
    (-f).sum (fun a b => b • x a) = -(f.sum (fun a b => b • x a)) := by
  calc
    (-f).sum (fun a b => b • x a) = ∑ a ∈ f.support, (-f a) • x a := by
      dsimp [Finsupp.sum]
      rw [Finsupp.support_neg]
    _ = ∑ a ∈ f.support, -(f a • x a) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp
    _ = -(f.sum (fun a b => b • x a)) := by
      dsimp [Finsupp.sum]
      exact (Finset.sum_neg_distrib (s := f.support) (fun a => f a • x a))

/-- The rel measure is transitive. -/
lemma pbwspan_Rel_trans {a b c : List ι} (hab : pbwspan_Rel a b) (hbc : pbwspan_Rel b c) :
    pbwspan_Rel a c := by
  unfold pbwspan_Rel pbwspan_μ at hab hbc ⊢
  exact _root_.trans hab hbc

/-- Length bound for the correction words. -/
lemma pbwspan_len_two (U0 v : List ι) (p q x0 x y : ι) :
    (U0 ++ p :: q :: v).length < (U0 ++ x0 :: x :: y :: v).length := by
  simp [List.length_append]

/-- Bracket coefficients are skew-symmetric. -/
lemma repr_bracket_neg (e : Module.Basis ι K L) (p q : ι) :
    e.repr ⁅e p, e q⁆ = -(e.repr ⁅e q, e p⁆) := by
  have hb : ⁅e p, e q⁆ = -⁅e q, e p⁆ := (lie_skew (e p) (e q)).symm
  rw [hb]
  exact map_neg (e.repr) ⁅e q, e p⁆

omit [CharZero K] [LinearOrder ι] in
/-- A linear map commutes with `Finsupp.sum`. -/
lemma map_finsupp_sum {N M : Type u} [AddCommGroup N] [Module K N] [AddCommGroup M]
    [Module K M] (φ : N →ₗ[K] M) (f : ι →₀ K) (x : ι → N) :
    φ (f.sum (fun k d => d • x k)) = f.sum (fun k d => d • φ (x k)) := by
  dsimp [Finsupp.sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul]

/-- Evaluating `e.repr` at an index commutes with `Finsupp.sum`. -/
lemma repr_eval_sum (e : Module.Basis ι K L) (f : ι →₀ K)
    (x : ι → L) (b : ι) :
    (e.repr (f.sum (fun k d => d • x k))) b = f.sum (fun k d => d • (e.repr (x k)) b) := by
  let ev : (ι →₀ K) →ₗ[K] K :=
    { toFun := fun g => g b
      map_add' := by intro g h; rfl
      map_smul' := by intro t g; rfl }
  have h := map_finsupp_sum (ev.comp (e.repr : L →ₗ[K] ι →₀ K)) f x
  change (e.repr (f.sum (fun k d => d • x k))) b = f.sum (fun k d => d • (e.repr (x k)) b)
  exact h

/-- Basis expansion of the coefficient of `[[e p, e q], e r]`. -/
lemma repr_lie_double_expand (e : Module.Basis ι K L) (p q r b : ι) :
    (e.repr ⁅⁅e p, e q⁆, e r⁆) b =
      (e.repr ⁅e p, e q⁆).sum (fun k d => d • (e.repr ⁅e k, e r⁆) b) := by
  have hsum : ⁅e p, e q⁆ = (e.repr ⁅e p, e q⁆).sum (fun k d => d • e k) := by
    rw [← Finsupp.linearCombination_apply]
    rw [← Module.Basis.repr_symm_apply]
    exact (LinearEquiv.symm_apply_apply e.repr ⁅e p, e q⁆).symm
  have hφ : (e.repr ⁅⁅e p, e q⁆, e r⁆) b =
      (e.repr ⁅(e.repr ⁅e p, e q⁆).sum (fun k d => d • e k), e r⁆) b := by
    exact congrArg (fun v : L => (e.repr ⁅v, e r⁆) b) hsum
  rw [hφ]
  let φ : L →ₗ[K] L :=
    { toFun := fun x => ⁅x, e r⁆
      map_add' := by intro x y; simp
      map_smul' := by intro t x; simp }
  change (e.repr (φ ((e.repr ⁅e p, e q⁆).sum (fun k d => d • e k)))) b =
    (e.repr ⁅e p, e q⁆).sum (fun k d => d • (e.repr ⁅e k, e r⁆) b)
  rw [map_finsupp_sum φ]
  exact repr_eval_sum e (e.repr ⁅e p, e q⁆) (fun k : ι => φ (e k)) b
/-- Negation can be moved inside a `Finsupp.sum`. -/
lemma finsupp_sum_neg_each {M : Type u} [AddCommGroup M] [Module K M] (f : ι →₀ K) (x : ι → M) :
    f.sum (fun a b => b • -x a) = -(f.sum (fun a b => b • x a)) := by
  calc
    f.sum (fun a b => b • -x a) = f.sum (fun a b => -(b • x a)) := by
      apply Finsupp.sum_congr
      intro a ha
      rw [smul_neg]
    _ = -(f.sum (fun a b => b • x a)) := by
      dsimp [Finsupp.sum]
      exact (Finset.sum_neg_distrib (s := f.support) (fun a => f a • x a))

/-- Negating the first factor of a double bracket. -/
lemma repr_double_neg (e : Module.Basis ι K L) (a b c m : ι) :
    (e.repr ⁅⁅e b, e a⁆, e c⁆) m =
      -((e.repr ⁅e a, e b⁆).sum (fun k d => d • (e.repr ⁅e k, e c⁆) m)) := by
  rw [repr_lie_double_expand e b a c m]
  rw [repr_bracket_neg e b a]
  exact finsupp_sum_neg (e.repr ⁅e a, e b⁆) (fun k => (e.repr ⁅e k, e c⁆) m)

/-- Coefficient identity used in the overlap case (a consequence of the Jacobi identity). -/
lemma overlapCoeff_zero (e : Module.Basis ι K L) (x0 x y b : ι) :
    (e.repr ⁅e x0, e x⁆).sum (fun k d => d • (e.repr ⁅e k, e y⁆) b) +
    (e.repr ⁅e x0, e y⁆).sum (fun k d => d • (e.repr ⁅e x, e k⁆) b) +
    (e.repr ⁅e x, e y⁆).sum (fun k d => d • (e.repr ⁅e k, e x0⁆) b) = 0 := by
  have h := bracketJacobi_coeff_outer e x0 x y b
  -- h : (repr [[x0,x],y]) b + (repr [[x,y],x0]) b + (repr [[y,x0],x]) b = 0
  have ht1 := repr_lie_double_expand e x0 x y b
  have ht2 := repr_lie_double_expand e x y x0 b
  have ht3 : (e.repr ⁅e x0, e y⁆).sum (fun k d => d • (e.repr ⁅e x, e k⁆) b) =
      (e.repr ⁅⁅e y, e x0⁆, e x⁆) b := by
    have hstep : (e.repr ⁅e x0, e y⁆).sum (fun k d => d • (e.repr ⁅e k, e x⁆) b) =
        -((e.repr ⁅e x0, e y⁆).sum (fun k d => d • (e.repr ⁅e x, e k⁆) b)) := by
      calc
        (e.repr ⁅e x0, e y⁆).sum (fun k d => d • (e.repr ⁅e k, e x⁆) b)
            = (e.repr ⁅e x0, e y⁆).sum (fun k d => d • -(e.repr ⁅e x, e k⁆) b) := by
              apply Finsupp.sum_congr
              intro k hk
              rw [repr_bracket_neg e k x]
              simp
        _ = -((e.repr ⁅e x0, e y⁆).sum (fun k d => d • (e.repr ⁅e x, e k⁆) b)) := by
              exact finsupp_sum_neg_each (e.repr ⁅e x0, e y⁆) (fun k => (e.repr ⁅e x, e k⁆) b)
    calc
      (e.repr ⁅e x0, e y⁆).sum (fun k d => d • (e.repr ⁅e x, e k⁆) b)
          = -((e.repr ⁅e x0, e y⁆).sum (fun k d => d • (e.repr ⁅e k, e x⁆) b)) := by
            have htmp := congrArg (fun t : K => -t) hstep
            -- htmp : -A = -(-B) with A := [k,x]-sum, B := [x,k]-sum ; simp: -A = B ; symm: B = -A
            simpa using htmp.symm
      _ = (e.repr ⁅⁅e y, e x0⁆, e x⁆) b := by
            exact (repr_double_neg e x0 y x b).symm
  calc
    (e.repr ⁅e x0, e x⁆).sum (fun k d => d • (e.repr ⁅e k, e y⁆) b) +
      (e.repr ⁅e x0, e y⁆).sum (fun k d => d • (e.repr ⁅e x, e k⁆) b) +
      (e.repr ⁅e x, e y⁆).sum (fun k d => d • (e.repr ⁅e k, e x0⁆) b)
        = (e.repr ⁅⁅e x0, e x⁆, e y⁆) b + (e.repr ⁅⁅e y, e x0⁆, e x⁆) b +
            (e.repr ⁅⁅e x, e y⁆, e x0⁆) b := by
            rw [ht1, ht3, ht2]
    _ = 0 := by
          rw [← h]
          ring
/-- The total correction in the overlap case vanishes (Jacobi in coefficient form). -/
lemma overlapCorr_zero (e : Module.Basis ι K L) (U0 v : List ι) (x0 x y : ι) :
    (e.repr ⁅e x0, e x⁆).sum
        (fun k d => d • (e.repr ⁅e k, e y⁆).sum (fun b e2 => e2 • sWord e (U0 ++ b :: v))) +
    (e.repr ⁅e x0, e y⁆).sum
        (fun k d => d • (e.repr ⁅e x, e k⁆).sum (fun b e2 => e2 • sWord e (U0 ++ b :: v))) +
    (e.repr ⁅e x, e y⁆).sum
        (fun k d => d • (e.repr ⁅e k, e x0⁆).sum (fun b e2 => e2 • sWord e (U0 ++ b :: v))) = 0 := by
  let LC : (ι →₀ K) →ₗ[K] TensorAlgebra K L :=
    Finsupp.linearCombination K (fun b => sWord e (U0 ++ b :: v))
  -- corr01 = LC(F3) with F3 := (repr[x0,x]).sum(fun k d => d • repr[k,y]) ; etc.
  have hLC1 : LC ((e.repr ⁅e x0, e x⁆).sum (fun k d => d • e.repr ⁅e k, e y⁆)) =
      (e.repr ⁅e x0, e x⁆).sum
        (fun k d => d • (e.repr ⁅e k, e y⁆).sum (fun b e2 => e2 • sWord e (U0 ++ b :: v))) := by
    calc
      LC ((e.repr ⁅e x0, e x⁆).sum (fun k d => d • e.repr ⁅e k, e y⁆))
          = (e.repr ⁅e x0, e x⁆).sum (fun k d => d • LC (e.repr ⁅e k, e y⁆)) := by
            exact map_finsupp_sum LC (e.repr ⁅e x0, e x⁆) (fun k => e.repr ⁅e k, e y⁆)
      _ = (e.repr ⁅e x0, e x⁆).sum
            (fun k d => d • (e.repr ⁅e k, e y⁆).sum (fun b e2 => e2 • sWord e (U0 ++ b :: v))) := by
            apply Finsupp.sum_congr
            intro k hk
            rfl
  have hLC2 : LC ((e.repr ⁅e x0, e y⁆).sum (fun k d => d • e.repr ⁅e x, e k⁆)) =
      (e.repr ⁅e x0, e y⁆).sum
        (fun k d => d • (e.repr ⁅e x, e k⁆).sum (fun b e2 => e2 • sWord e (U0 ++ b :: v))) := by
    calc
      LC ((e.repr ⁅e x0, e y⁆).sum (fun k d => d • e.repr ⁅e x, e k⁆))
          = (e.repr ⁅e x0, e y⁆).sum (fun k d => d • LC (e.repr ⁅e x, e k⁆)) := by
            exact map_finsupp_sum LC (e.repr ⁅e x0, e y⁆) (fun k => e.repr ⁅e x, e k⁆)
      _ = (e.repr ⁅e x0, e y⁆).sum
            (fun k d => d • (e.repr ⁅e x, e k⁆).sum (fun b e2 => e2 • sWord e (U0 ++ b :: v))) := by
            apply Finsupp.sum_congr
            intro k hk
            rfl
  have hLC3 : LC ((e.repr ⁅e x, e y⁆).sum (fun k d => d • e.repr ⁅e k, e x0⁆)) =
      (e.repr ⁅e x, e y⁆).sum
        (fun k d => d • (e.repr ⁅e k, e x0⁆).sum (fun b e2 => e2 • sWord e (U0 ++ b :: v))) := by
    calc
      LC ((e.repr ⁅e x, e y⁆).sum (fun k d => d • e.repr ⁅e k, e x0⁆))
          = (e.repr ⁅e x, e y⁆).sum (fun k d => d • LC (e.repr ⁅e k, e x0⁆)) := by
            exact map_finsupp_sum LC (e.repr ⁅e x, e y⁆) (fun k => e.repr ⁅e k, e x0⁆)
      _ = (e.repr ⁅e x, e y⁆).sum
            (fun k d => d • (e.repr ⁅e k, e x0⁆).sum (fun b e2 => e2 • sWord e (U0 ++ b :: v))) := by
            apply Finsupp.sum_congr
            intro k hk
            rfl
  have hF : ((e.repr ⁅e x0, e x⁆).sum (fun k d => d • e.repr ⁅e k, e y⁆) +
      (e.repr ⁅e x0, e y⁆).sum (fun k d => d • e.repr ⁅e x, e k⁆)) +
      (e.repr ⁅e x, e y⁆).sum (fun k d => d • e.repr ⁅e k, e x0⁆) = 0 := by
    apply Finsupp.ext
    intro b
    have hb := overlapCoeff_zero e x0 x y b
    simp [Finsupp.add_apply, Finsupp.sum_apply]
    simpa using hb
  rw [← hLC1, ← hLC2, ← hLC3]
  rw [← LC.map_add, ← LC.map_add]
  rw [hF]
  simp


/-- The overlap (critical-pair) case: three adjacent letters `x0 > x > y`. -/
lemma sWord_overlap_case (U0 v : List ι) (x0 x y : ι) (hxx0 : x < x0) (hyx : y < x)
    (hInd : ∀ w' : List ι, pbwspan_Rel w' (U0 ++ x0 :: x :: y :: v) →
       ∀ (u v' : List ι) (a b : ι), b < a → w' = u ++ a :: b :: v' →
          sWord e w' = sWord e (u ++ b :: a :: v') +
            (e.repr ⁅e a, e b⁆).sum (fun k d => d • sWord e (u ++ k :: v'))) :
    sWord e (U0 ++ x :: x0 :: y :: v) +
        (e.repr ⁅e x0, e x⁆).sum (fun k d => d • sWord e (U0 ++ k :: y :: v)) =
      sWord e (U0 ++ x0 :: y :: x :: v) +
        (e.repr ⁅e x, e y⁆).sum (fun k d => d • sWord e (U0 ++ x0 :: k :: v)) := by
  classical
  let c01 : ι →₀ K := e.repr ⁅e x0, e x⁆
  let c02 : ι →₀ K := e.repr ⁅e x0, e y⁆
  let c12 : ι →₀ K := e.repr ⁅e x, e y⁆
  have hyx0 : y < x0 := lt_trans hyx hxx0
  -- (1) σ(U0++x::x0::y::v) = σ(U0++x::y::x0::v) + c02 · σ(U0++x::k::v)
  have hA : sWord e (U0 ++ x :: x0 :: y :: v) =
      sWord e (U0 ++ x :: y :: x0 :: v) +
        c02.sum (fun k d => d • sWord e (U0 ++ x :: k :: v)) := by
    have hRel : pbwspan_Rel (U0 ++ x :: x0 :: y :: v) (U0 ++ x0 :: x :: y :: v) := by
      simpa [List.append_assoc] using (pbwspan_Rel_swap x0 x hxx0 U0 (y :: v))
    simpa [c02, List.append_assoc] using
      (hInd (U0 ++ x :: x0 :: y :: v) hRel (U0 ++ [x]) v x0 y hyx0
        (by simp [List.append_assoc]))
  -- (2) σ(U0++x::y::x0::v) = σ(U0++y::x::x0::v) + c12 · σ(U0++k::x0::v)
  have hB : sWord e (U0 ++ x :: y :: x0 :: v) =
      sWord e (U0 ++ y :: x :: x0 :: v) +
        c12.sum (fun k d => d • sWord e (U0 ++ k :: x0 :: v)) := by
    have hRel1 : pbwspan_Rel (U0 ++ x :: y :: x0 :: v) (U0 ++ x :: x0 :: y :: v) := by
      simpa [List.append_assoc] using (pbwspan_Rel_swap x0 y hyx0 (U0 ++ [x]) v)
    have hRel2 : pbwspan_Rel (U0 ++ x :: x0 :: y :: v) (U0 ++ x0 :: x :: y :: v) := by
      simpa [List.append_assoc] using (pbwspan_Rel_swap x0 x hxx0 U0 (y :: v))
    have hRel : pbwspan_Rel (U0 ++ x :: y :: x0 :: v) (U0 ++ x0 :: x :: y :: v) :=
      pbwspan_Rel_trans hRel1 hRel2
    simpa [c12, List.append_assoc] using
      (hInd (U0 ++ x :: y :: x0 :: v) hRel U0 (x0 :: v) x y hyx rfl)
  -- (3) σ(U0++x0::y::x::v) = σ(U0++y::x0::x::v) + c02 · σ(U0++k::x::v)
  have hC : sWord e (U0 ++ x0 :: y :: x :: v) =
      sWord e (U0 ++ y :: x0 :: x :: v) +
        c02.sum (fun k d => d • sWord e (U0 ++ k :: x :: v)) := by
    have hRel : pbwspan_Rel (U0 ++ x0 :: y :: x :: v) (U0 ++ x0 :: x :: y :: v) := by
      simpa [List.append_assoc] using (pbwspan_Rel_swap x y hyx (U0 ++ [x0]) v)
    simpa [c02, List.append_assoc] using
      (hInd (U0 ++ x0 :: y :: x :: v) hRel U0 (x :: v) x0 y hyx0 rfl)
  -- (4) σ(U0++y::x0::x::v) = σ(U0++y::x::x0::v) + c01 · σ(U0++y::k::v)
  have hD : sWord e (U0 ++ y :: x0 :: x :: v) =
      sWord e (U0 ++ y :: x :: x0 :: v) +
        c01.sum (fun k d => d • sWord e (U0 ++ y :: k :: v)) := by
    have hRel1 : pbwspan_Rel (U0 ++ y :: x0 :: x :: v) (U0 ++ x0 :: y :: x :: v) := by
      simpa [List.append_assoc] using (pbwspan_Rel_swap x0 y hyx0 U0 (x :: v))
    have hRel2 : pbwspan_Rel (U0 ++ x0 :: y :: x :: v) (U0 ++ x0 :: x :: y :: v) := by
      simpa [List.append_assoc] using (pbwspan_Rel_swap x y hyx (U0 ++ [x0]) v)
    have hRel : pbwspan_Rel (U0 ++ y :: x0 :: x :: v) (U0 ++ x0 :: x :: y :: v) :=
      pbwspan_Rel_trans hRel1 hRel2
    simpa [c01, List.append_assoc] using
      (hInd (U0 ++ y :: x0 :: x :: v) hRel (U0 ++ [y]) v x0 x hxx0
        (by simp [List.append_assoc]))
  -- (5) uniform two-letter swap identity (valid for all orders of p,q)
  have hU1 : ∀ p q : ι,
      sWord e (U0 ++ p :: q :: v) = sWord e (U0 ++ q :: p :: v) +
        (e.repr ⁅e p, e q⁆).sum (fun b d => d • sWord e (U0 ++ b :: v)) := by
    intro p q
    by_cases hpq : q < p
    · have hRel : pbwspan_Rel (U0 ++ p :: q :: v) (U0 ++ x0 :: x :: y :: v) := by
        exact pbwspan_Rel_of_len_lt (pbwspan_len_two U0 v p q x0 x y)
      simpa [List.append_assoc] using (hInd (U0 ++ p :: q :: v) hRel U0 v p q hpq rfl)
    · have hpqle : p ≤ q := le_of_not_gt hpq
      by_cases hpEq : p = q
      · rw [hpEq]
        simp [lie_self]
      · have hlt : p < q := lt_of_le_of_ne hpqle hpEq
        have hRel : pbwspan_Rel (U0 ++ q :: p :: v) (U0 ++ x0 :: x :: y :: v) := by
          exact pbwspan_Rel_of_len_lt (pbwspan_len_two U0 v q p x0 x y)
        have hE := hInd (U0 ++ q :: p :: v) hRel U0 v q p hlt rfl
        calc
          sWord e (U0 ++ p :: q :: v)
              = sWord e (U0 ++ q :: p :: v) -
                  (e.repr ⁅e q, e p⁆).sum (fun b d => d • sWord e (U0 ++ b :: v)) := by
                  rw [hE]
                  abel
          _ = sWord e (U0 ++ q :: p :: v) +
              (e.repr ⁅e p, e q⁆).sum (fun b d => d • sWord e (U0 ++ b :: v)) := by
              have hnegsum : -((e.repr ⁅e q, e p⁆).sum
                    (fun b d => d • sWord e (U0 ++ b :: v))) =
                  (e.repr ⁅e p, e q⁆).sum (fun b d => d • sWord e (U0 ++ b :: v)) := by
                rw [repr_bracket_neg e p q]
                exact (finsupp_sum_neg (e.repr ⁅e q, e p⁆) (fun b => sWord e (U0 ++ b :: v))).symm
              rw [sub_eq_add_neg, hnegsum]
  let corr12 : TensorAlgebra K L := c12.sum
    (fun k d => d • (e.repr ⁅e k, e x0⁆).sum (fun b e2 => e2 • sWord e (U0 ++ b :: v)))
  let corr02 : TensorAlgebra K L := c02.sum
    (fun k d => d • (e.repr ⁅e x, e k⁆).sum (fun b e2 => e2 • sWord e (U0 ++ b :: v)))
  let corr01 : TensorAlgebra K L := c01.sum
    (fun k d => d • (e.repr ⁅e k, e y⁆).sum (fun b e2 => e2 • sWord e (U0 ++ b :: v)))
  have hN12 : c12.sum (fun k d => d • sWord e (U0 ++ k :: x0 :: v)) =
      c12.sum (fun k d => d • sWord e (U0 ++ x0 :: k :: v)) + corr12 := by
    calc
      c12.sum (fun k d => d • sWord e (U0 ++ k :: x0 :: v))
          = c12.sum (fun k d => d • (sWord e (U0 ++ x0 :: k :: v) +
              (e.repr ⁅e k, e x0⁆).sum (fun b e2 => e2 • sWord e (U0 ++ b :: v)))) := by
            apply Finsupp.sum_congr
            intro k hk
            rw [hU1 k x0]
      _ = c12.sum (fun k d => d • sWord e (U0 ++ x0 :: k :: v)) + corr12 := by
            simpa [corr12] using
              (finsupp_smul_add c12 (fun k => sWord e (U0 ++ x0 :: k :: v))
                (fun k => (e.repr ⁅e k, e x0⁆).sum (fun b e2 => e2 • sWord e (U0 ++ b :: v))))
  have hN02 : c02.sum (fun k d => d • sWord e (U0 ++ x :: k :: v)) =
      c02.sum (fun k d => d • sWord e (U0 ++ k :: x :: v)) + corr02 := by
    calc
      c02.sum (fun k d => d • sWord e (U0 ++ x :: k :: v))
          = c02.sum (fun k d => d • (sWord e (U0 ++ k :: x :: v) +
              (e.repr ⁅e x, e k⁆).sum (fun b e2 => e2 • sWord e (U0 ++ b :: v)))) := by
            apply Finsupp.sum_congr
            intro k hk
            rw [hU1 x k]
      _ = c02.sum (fun k d => d • sWord e (U0 ++ k :: x :: v)) + corr02 := by
            simpa [corr02] using
              (finsupp_smul_add c02 (fun k => sWord e (U0 ++ k :: x :: v))
                (fun k => (e.repr ⁅e x, e k⁆).sum (fun b e2 => e2 • sWord e (U0 ++ b :: v))))
  have hN01 : c01.sum (fun k d => d • sWord e (U0 ++ k :: y :: v)) =
      c01.sum (fun k d => d • sWord e (U0 ++ y :: k :: v)) + corr01 := by
    calc
      c01.sum (fun k d => d • sWord e (U0 ++ k :: y :: v))
          = c01.sum (fun k d => d • (sWord e (U0 ++ y :: k :: v) +
              (e.repr ⁅e k, e y⁆).sum (fun b e2 => e2 • sWord e (U0 ++ b :: v)))) := by
            apply Finsupp.sum_congr
            intro k hk
            rw [hU1 k y]
      _ = c01.sum (fun k d => d • sWord e (U0 ++ y :: k :: v)) + corr01 := by
            simpa [corr01] using
              (finsupp_smul_add c01 (fun k => sWord e (U0 ++ y :: k :: v))
                (fun k => (e.repr ⁅e k, e y⁆).sum (fun b e2 => e2 • sWord e (U0 ++ b :: v))))
  have hcorrZ : corr01 + corr02 + corr12 = 0 := by
    simpa [corr12, corr02, corr01, c01, c02, c12] using (overlapCorr_zero e U0 v x0 x y)
  calc
    sWord e (U0 ++ x :: x0 :: y :: v) +
        c01.sum (fun k d => d • sWord e (U0 ++ k :: y :: v))
        = (sWord e (U0 ++ y :: x :: x0 :: v) +
            c12.sum (fun k d => d • sWord e (U0 ++ k :: x0 :: v)) +
            c02.sum (fun k d => d • sWord e (U0 ++ x :: k :: v))) +
          c01.sum (fun k d => d • sWord e (U0 ++ k :: y :: v)) := by
            rw [hA, hB]
    _ = (sWord e (U0 ++ y :: x :: x0 :: v) +
          (c12.sum (fun k d => d • sWord e (U0 ++ x0 :: k :: v)) + corr12) +
            c02.sum (fun k d => d • sWord e (U0 ++ x :: k :: v))) +
          c01.sum (fun k d => d • sWord e (U0 ++ k :: y :: v)) := by
            rw [hN12]
    _ = (sWord e (U0 ++ y :: x :: x0 :: v) +
          (c12.sum (fun k d => d • sWord e (U0 ++ x0 :: k :: v)) + corr12) +
          (c02.sum (fun k d => d • sWord e (U0 ++ k :: x :: v)) + corr02)) +
          c01.sum (fun k d => d • sWord e (U0 ++ k :: y :: v)) := by
            rw [hN02]
    _ = (sWord e (U0 ++ y :: x :: x0 :: v) +
          (c12.sum (fun k d => d • sWord e (U0 ++ x0 :: k :: v)) + corr12) +
          (c02.sum (fun k d => d • sWord e (U0 ++ k :: x :: v)) + corr02)) +
          (c01.sum (fun k d => d • sWord e (U0 ++ y :: k :: v)) + corr01) := by
            rw [hN01]
    _ = ((sWord e (U0 ++ y :: x :: x0 :: v) +
          c01.sum (fun k d => d • sWord e (U0 ++ y :: k :: v))) +
          c02.sum (fun k d => d • sWord e (U0 ++ k :: x :: v))) +
          c12.sum (fun k d => d • sWord e (U0 ++ x0 :: k :: v)) +
          (corr01 + corr02 + corr12) := by
            ac_rfl
    _ = ((sWord e (U0 ++ y :: x :: x0 :: v) +
          c01.sum (fun k d => d • sWord e (U0 ++ y :: k :: v))) +
          c02.sum (fun k d => d • sWord e (U0 ++ k :: x :: v))) +
          c12.sum (fun k d => d • sWord e (U0 ++ x0 :: k :: v)) := by
            rw [hcorrZ]
            simp
    _ = sWord e (U0 ++ x0 :: y :: x :: v) +
          c12.sum (fun k d => d • sWord e (U0 ++ x0 :: k :: v)) := by
            rw [hC, hD]
/-- The key confluence lemma (swap identity at every descent). -/
lemma sWord_swap (u v : List ι) (x y : ι) (hxy : y < x) :
    sWord e (u ++ x :: y :: v) = sWord e (u ++ y :: x :: v) +
      (e.repr ⁅e x, e y⁆).sum (fun k d => d • sWord e (u ++ k :: v)) := by
  classical
  let P : List ι → Prop := fun w => ∀ (u v : List ι) (x y : ι), y < x → w = u ++ x :: y :: v →
      sWord e w = sWord e (u ++ y :: x :: v) +
        (e.repr ⁅e x, e y⁆).sum (fun k d => d • sWord e (u ++ k :: v))
  have hmain : ∀ w : List ι, P w := by
    intro w
    refine pbwspan_wfRel.induction (C := P) w ?_
    intro z ih u v x y hxy hz
    rw [hz]
    have hnot : ¬ pbwspan_sorted (u ++ x :: y :: v) := not_sorted_of_desc_concat hxy
    rw [sWord_expand e (u ++ x :: y :: v) hnot]
    set D := fdd (u ++ x :: y :: v) hnot
    let U0 := D.1.1
    let x0 := D.1.2.1
    let y0 := D.1.2.2.1
    let V0 := D.1.2.2.2
    have hwD : u ++ x :: y :: v = U0 ++ x0 :: y0 :: V0 := by
      simpa [U0, x0, y0, V0, D] using D.2.1
    have hy0x0 : y0 < x0 := by
      simpa [x0, y0, D] using D.2.2.1
    have hsU0 : pbwspan_sorted U0 := by
      simpa [U0, D] using D.2.2.2.1
    have hux0 : ∀ z ∈ U0, z ≤ x0 := by
      intro z hz
      simpa [U0, x0, D] using D.2.2.2.2 z hz
    rcases prefix_comparable u (x :: y :: v) U0 (x0 :: y0 :: V0) hwD with ⟨t, hUeq⟩ | ⟨t, hUeq2⟩
    · -- Case 1: U0 = u ++ t
      by_cases ht : t = []
      · -- t = [] : target = first descent: U0 = u, x0 = x, y0 = y, V0 = v
        have hU : U0 = u := by
          rw [hUeq, ht]
          simp
        have hxyz : x :: y :: v = x0 :: y0 :: V0 := by
          exact append_left_cancel' u (x :: y :: v) (x0 :: y0 :: V0) (by simpa [hU] using hwD)
        have hx0x : x0 = x := (List.cons.inj hxyz).1.symm
        have hy0y : y0 = y := (List.cons.inj (List.cons.inj hxyz).2).1.symm
        have hV0 : V0 = v := (List.cons.inj (List.cons.inj hxyz).2).2.symm
        have hD1 : D.1.1 = u := by simpa [U0] using hU
        have hD2 : D.1.2.1 = x := by simpa [x0] using hx0x
        have hD3 : D.1.2.2.1 = y := by simpa [y0] using hy0y
        have hD4 : D.1.2.2.2 = v := by simpa [V0] using hV0
        rw [hD1, hD2, hD3, hD4]
      · -- U0 = u ++ t with t ≠ [] : target (x,y) lies strictly inside the sorted prefix U0;
        -- then x ≤ y, contradicting y < x.
        exfalso
        have hRest : x :: y :: v = t ++ x0 :: y0 :: V0 := by
          exact append_left_cancel' u (x :: y :: v) (t ++ x0 :: y0 :: V0)
            (by simpa [hUeq] using hwD)
        rcases List.exists_cons_of_ne_nil ht with ⟨c, t', ht_eq⟩
        rw [ht_eq] at hRest
        have hc : c = x := by
          have hh : x :: y :: v = c :: (t' ++ x0 :: y0 :: V0) := by simpa using hRest
          exact (List.cons.inj hh).1.symm
        have hRest2 : y :: v = t' ++ x0 :: y0 :: V0 := by
          have hh : x :: y :: v = x :: (t' ++ x0 :: y0 :: V0) := by simpa [hc] using hRest
          exact (List.cons.inj hh).2
        by_cases ht' : t' = []
        · -- t' = []: y = x0 and x ∈ U0 with x ≤ x0 (all elements of U0 ≤ x0)
          have hy : y = x0 := by
            have hh : y :: v = x0 :: y0 :: V0 := by simpa [ht'] using hRest2
            exact (List.cons.inj hh).1
          have hxmem : x ∈ U0 := by
            rw [hUeq, ht_eq, hc, ht']
            simp
          have hx_le : x ≤ x0 := hux0 x hxmem
          exact (not_le_of_gt hxy) (by rw [hy]; exact hx_le)
        · -- t' ≠ []: y ∈ t', and U0 = u ++ x :: t' sorted gives x ≤ y
          rcases List.exists_cons_of_ne_nil ht' with ⟨d, t'', ht'_eq⟩
          rw [ht'_eq] at hRest2
          have hy : y = d := by
            have hh : y :: v = d :: (t'' ++ x0 :: y0 :: V0) := by simpa using hRest2
            exact (List.cons.inj hh).1
          have hymem : y ∈ t' := by
            rw [hy, ht'_eq]
            simp
          have hx_le_y : x ≤ y := by
            have hsU : pbwspan_sorted (u ++ x :: t') := by
              simpa [hUeq, ht_eq, hc] using hsU0
            exact le_of_mem_sorted_after hsU hymem
          exact (not_le_of_gt hxy) hx_le_y
    · -- Case 2: u = U0 ++ t
      have hRest : t ++ x :: y :: v = x0 :: y0 :: V0 := by
        exact append_left_cancel' U0 (t ++ x :: y :: v) (x0 :: y0 :: V0)
          (by simpa [hUeq2] using hwD)
      by_cases ht0 : t = []
      · -- t = []: again target = first descent (u = U0)
        have hU : U0 = u := by
          rw [hUeq2, ht0]
          simp
        have hxyz : x :: y :: v = x0 :: y0 :: V0 := by
          exact append_left_cancel' u (x :: y :: v) (x0 :: y0 :: V0) (by simpa [hU, hwD])
        have hx0x : x0 = x := (List.cons.inj hxyz).1.symm
        have hy0y : y0 = y := (List.cons.inj (List.cons.inj hxyz).2).1.symm
        have hV0 : V0 = v := (List.cons.inj (List.cons.inj hxyz).2).2.symm
        have hD1 : D.1.1 = u := by simpa [U0] using hU
        have hD2 : D.1.2.1 = x := by simpa [x0] using hx0x
        have hD3 : D.1.2.2.1 = y := by simpa [y0] using hy0y
        have hD4 : D.1.2.2.2 = v := by simpa [V0] using hV0
        rw [hD1, hD2, hD3, hD4]
      · -- t ≠ []: t = x0 :: t1 (head x0), subcases t1 = [] (overlap) or t1 = y0 :: t2 (disjoint)
        rcases List.exists_cons_of_ne_nil ht0 with ⟨c, t1, ht_eq⟩
        rw [ht_eq] at hRest
        have hc : c = x0 := by
          have hh : c :: (t1 ++ x :: y :: v) = x0 :: y0 :: V0 := by simpa using hRest
          exact (List.cons.inj hh).1
        have hRest2 : t1 ++ x :: y :: v = y0 :: V0 := by
          have hh : c :: (t1 ++ x :: y :: v) = x0 :: y0 :: V0 := by simpa using hRest
          exact (List.cons.inj hh).2
        by_cases ht1 : t1 = []
        · -- overlap: x = y0 (and V0 = y :: v, u = U0 ++ [x0])
          have hxy0 : x = y0 := by
            have hh : x :: y :: v = y0 :: V0 := by simpa [ht1] using hRest2
            exact (List.cons.inj hh).1
          have hV0y : V0 = y :: v := by
            have hh : x :: y :: v = y0 :: V0 := by simpa [ht1] using hRest2
            exact (List.cons.inj hh).2.symm
          have hu3 : u = U0 ++ [x0] := by
            simp [hUeq2, ht_eq, hc, ht1]
          have hxx0' : x < x0 := by
            rw [hxy0]
            exact hy0x0
          have hz3 : u ++ x :: y :: v = U0 ++ x0 :: x :: y :: v := by
            rw [hu3]
            simp [List.append_assoc]
          have hrel' : ∀ w' : List ι,
              pbwspan_Rel w' (U0 ++ x0 :: x :: y :: v) →
                ∀ (u0 v0 : List ι) (a b : ι), b < a → w' = u0 ++ a :: b :: v0 →
                  sWord e w' = sWord e (u0 ++ b :: a :: v0) +
                    (e.repr ⁅e a, e b⁆).sum (fun k d => d • sWord e (u0 ++ k :: v0)) := by
            intro w' hw' u0 v0 a b hba hw'eq
            exact ih w' (Rel_cast (hz.trans hz3) hw') u0 v0 a b hba hw'eq
          have hres : sWord e (U0 ++ x :: x0 :: y :: v) +
                (e.repr ⁅e x0, e x⁆).sum (fun k d => d • sWord e (U0 ++ k :: y :: v)) =
              sWord e (U0 ++ x0 :: y :: x :: v) +
                (e.repr ⁅e x, e y⁆).sum (fun k d => d • sWord e (U0 ++ x0 :: k :: v)) := by
            exact sWord_overlap_case e U0 v x0 x y hxx0' hxy hrel'
          have hD1U : D.1.1 = U0 := rfl
          have hD2U : D.1.2.1 = x0 := rfl
          have hD3U : D.1.2.2.1 = y0 := rfl
          have hV3 : D.1.2.2.2 = y :: v := by
            simpa [V0] using hV0y
          simpa [hu3, hxy0, hV3, List.append_assoc, hD1U, hD2U, hD3U] using hres
        · -- disjoint: t1 = y0 :: t2
          rcases List.exists_cons_of_ne_nil ht1 with ⟨d, t2, ht1_eq⟩
          rw [ht1_eq] at hRest2
          have hd : d = y0 := by
            have hh : d :: (t2 ++ x :: y :: v) = y0 :: V0 := by simpa using hRest2
            exact (List.cons.inj hh).1
          have hRest3 : t2 ++ x :: y :: v = V0 := by
            have hh : d :: (t2 ++ x :: y :: v) = y0 :: V0 := by simpa using hRest2
            exact (List.cons.inj hh).2
          have hu2 : u = U0 ++ x0 :: y0 :: t2 := by
            rw [hUeq2, ht_eq, hc, ht1_eq, hd]
          have hz' : u ++ x :: y :: v = U0 ++ x0 :: y0 :: t2 ++ x :: y :: v := by
            rw [hu2]
          have hrel : ∀ w' : List ι,
              pbwspan_Rel w' (U0 ++ x0 :: y0 :: t2 ++ x :: y :: v) →
                ∀ (u0 v0 : List ι) (a b : ι), b < a → w' = u0 ++ a :: b :: v0 →
                  sWord e w' = sWord e (u0 ++ b :: a :: v0) +
                    (e.repr ⁅e a, e b⁆).sum (fun k d => d • sWord e (u0 ++ k :: v0)) := by
            intro w' hw' u0 v0 a b hba hw'eq
            exact ih w' (Rel_cast (hz.trans hz') hw') u0 v0 a b hba hw'eq
          have hres : sWord e (U0 ++ y0 :: x0 :: t2 ++ x :: y :: v) +
                (e.repr ⁅e x0, e y0⁆).sum
                  (fun k d => d • sWord e (U0 ++ k :: t2 ++ x :: y :: v)) =
              sWord e (U0 ++ x0 :: y0 :: t2 ++ y :: x :: v) +
                (e.repr ⁅e x, e y⁆).sum
                  (fun k d => d • sWord e (U0 ++ x0 :: y0 :: t2 ++ k :: v)) := by
            exact sWord_disjoint_case e U0 t2 v x y x0 y0 hy0x0 hxy hrel
          have hD1U : D.1.1 = U0 := rfl
          have hD2U : D.1.2.1 = x0 := rfl
          have hD3U : D.1.2.2.1 = y0 := rfl
          have hV3 : D.1.2.2.2 = t2 ++ x :: y :: v := by
            simpa [V0] using hRest3.symm
          simpa [hu2, hV3, List.append_assoc, hD1U, hD2U, hD3U] using hres
  exact hmain (u ++ x :: y :: v) u v x y hxy rfl

end Sigma

section FinalSetup

open TensorAlgebra
open UniversalEnvelopingAlgebra

variable {K L ι : Type u} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [LinearOrder ι]

/-- The word `w` as an element of the tensor algebra. -/
noncomputable def tfWord (e : Module.Basis ι K L) (w : List ι) : TensorAlgebra K L :=
  (w.map (fun i => TensorAlgebra.ι K (e i))).prod

/-- The straightening map is the identity on the tensor word of a sorted word. -/
lemma tfWord_eq_tensorAlgebra (e : Module.Basis ι K L) (w : List ι) :
    tfWord e w = e.tensorAlgebra w := by
  exact Commons.LinearAlgebra.TensorAlgebra.word_eq_basis e w

/-- `sigmaLin` extends `sWord`. -/
lemma sigmaLin_tfWord (e : Module.Basis ι K L) (w : List ι) :
    sigmaLin e (tfWord e w) = sWord e w := by
  rw [tfWord_eq_tensorAlgebra]
  unfold sigmaLin
  have hc := Module.Basis.constr_apply (b := e.tensorAlgebra) (S := K) (f := sWord e)
    (x := e.tensorAlgebra w)
  change Module.Basis.constr e.tensorAlgebra K (sWord e) (e.tensorAlgebra w) = sWord e w
  rw [hc]
  have hr : (e.tensorAlgebra).repr (e.tensorAlgebra w) =
      Finsupp.single (w : FreeMonoid ι) (1 : K) := by
    exact Module.Basis.repr_self e.tensorAlgebra (w : FreeMonoid ι)
  rw [hr]
  change Finsupp.linearCombination K (fun b => sWord e b)
      (Finsupp.single (w : FreeMonoid ι) (1 : K)) = sWord e w
  simp

/-- The tensor word of a sorted word straightens to itself. -/
lemma sigmaLin_sorted (e : Module.Basis ι K L) (w : List ι) (hs : pbwspan_sorted w) :
    sigmaLin e (tfWord e w) = tfWord e w := by
  rw [sigmaLin_tfWord]
  rw [sWord_sorted e w hs]
  exact (tfWord_eq_tensorAlgebra e w).symm

end FinalSetup

section SigmaRelator

variable {K L ι : Type u} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [LinearOrder ι]

lemma tfWord_append (e : Module.Basis ι K L) (u v : List ι) :
    tfWord e (u ++ v) = tfWord e u * tfWord e v := by
  simp [tfWord]

def taRel (e : Module.Basis ι K L) (i j : ι) : TensorAlgebra K L :=
  TensorAlgebra.ι K (e i) * TensorAlgebra.ι K (e j) -
    TensorAlgebra.ι K (e j) * TensorAlgebra.ι K (e i) - TensorAlgebra.ι K ⁅e i, e j⁆

lemma iota_bracket_expand (e : Module.Basis ι K L) (x y : ι) :
    TensorAlgebra.ι K ⁅e x, e y⁆ =
      (e.repr ⁅e x, e y⁆).sum (fun k d => d • TensorAlgebra.ι K (e k)) := by
  let c : ι →₀ K := e.repr ⁅e x, e y⁆
  have hsum : ⁅e x, e y⁆ = c.sum (fun k d => d • e k) := by
    dsimp [c]
    rw [← Finsupp.linearCombination_apply]
    rw [← Module.Basis.repr_symm_apply]
    exact (LinearEquiv.symm_apply_apply e.repr ⁅e x, e y⁆).symm
  have hι : TensorAlgebra.ι K ⁅e x, e y⁆ =
      c.sum (fun k d => d • TensorAlgebra.ι K (e k)) := by
    rw [hsum]
    change (TensorAlgebra.ι K)
        (∑ k ∈ c.support, c k • e k) =
      c.sum (fun k d => d • TensorAlgebra.ι K (e k))
    rw [map_sum (TensorAlgebra.ι K)]
    simp only [map_smul]
    rfl
  simpa [c] using hι

lemma sigmaLin_tfWord_append_letter (e : Module.Basis ι K L) (u v : List ι) (i j : ι) :
    sigmaLin e (((tfWord e u * TensorAlgebra.ι K (e i)) * TensorAlgebra.ι K (e j)) * tfWord e v)
      = sWord e (u ++ i :: j :: v) := by
  have harg : ((tfWord e u * TensorAlgebra.ι K (e i)) * TensorAlgebra.ι K (e j)) * tfWord e v
      = tfWord e (u ++ i :: j :: v) := by
    calc
      ((tfWord e u * TensorAlgebra.ι K (e i)) * TensorAlgebra.ι K (e j)) * tfWord e v
          = ((tfWord e u * tfWord e [i]) * tfWord e [j]) * tfWord e v := by
              rw [show TensorAlgebra.ι K (e i) = tfWord e [i] by simp [tfWord]]
              rw [show TensorAlgebra.ι K (e j) = tfWord e [j] by simp [tfWord]]
      _ = (tfWord e (u ++ [i]) * tfWord e [j]) * tfWord e v := by
              rw [← tfWord_append e u [i]]
      _ = tfWord e ((u ++ [i] ++ [j]) ++ v) := by
              rw [← tfWord_append e (u ++ [i]) [j]]
              rw [← tfWord_append e (u ++ [i] ++ [j]) v]
      _ = tfWord e (u ++ i :: j :: v) := by
              congr 1
              simp [List.append_assoc]
  rw [harg]
  exact sigmaLin_tfWord e (u ++ i :: j :: v)

lemma sWord_swap_general (e : Module.Basis ι K L) (u v : List ι) (i j : ι) :
    sWord e (u ++ i :: j :: v) = sWord e (u ++ j :: i :: v) +
      (e.repr ⁅e i, e j⁆).sum (fun k d => d • sWord e (u ++ k :: v)) := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · -- i < j
    have hswap := sWord_swap e u v j i hlt
    let c : ι →₀ K := e.repr ⁅e i, e j⁆
    let c' : ι →₀ K := e.repr ⁅e j, e i⁆
    have hc' : c' = -c := by
      dsimp [c, c']
      exact repr_bracket_neg e j i
    have hsumF : c'.sum (fun k d => d • sWord e (u ++ k :: v)) =
        - c.sum (fun k d => d • sWord e (u ++ k :: v)) := by
      rw [hc']
      exact finsupp_sum_neg c (fun k => sWord e (u ++ k :: v))
    have hBC : sWord e (u ++ j :: i :: v) + c.sum (fun k d => d • sWord e (u ++ k :: v))
        = sWord e (u ++ i :: j :: v) := by
      calc
        sWord e (u ++ j :: i :: v) + c.sum (fun k d => d • sWord e (u ++ k :: v))
            = (sWord e (u ++ i :: j :: v)
                + c'.sum (fun k d => d • sWord e (u ++ k :: v)))
              + c.sum (fun k d => d • sWord e (u ++ k :: v)) := by
                rw [hswap]
        _ = sWord e (u ++ i :: j :: v) + 0 := by
                rw [hsumF]
                abel
        _ = sWord e (u ++ i :: j :: v) := by rw [add_zero]
    exact hBC.symm
  · -- i = j
    subst j
    have hc0 : (e.repr ⁅e i, e i⁆) = 0 := by
      rw [lie_self]
      simp
    simp [hc0]
  · -- j < i
    exact sWord_swap e u v i j hgt

section RelTests
open TensorAlgebra
open UniversalEnvelopingAlgebra

variable {K L ι : Type u} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [LinearOrder ι]


/-- relator element for arbitrary elements of L -/
def taRelFull (x y : L) : TensorAlgebra K L :=
  TensorAlgebra.ι K x * TensorAlgebra.ι K y -
    TensorAlgebra.ι K y * TensorAlgebra.ι K x - TensorAlgebra.ι K ⁅x, y⁆

lemma taRel_eq_full (e : Module.Basis ι K L) (i j : ι) :
    taRel e i j = taRelFull (e i) (e j) := rfl

/-- The map y ↦ ⁅e p, y⁆ is linear. -/
def brRight (p : L) : L →ₗ[K] L where
  toFun := fun y => ⁅p, y⁆
  map_add' := by intro x y; simp [lie_add]
  map_smul' := by intro c x; simp [lie_smul]

/-- The map x ↦ ⁅x, y⁆ is linear. -/
def brLeft (y : L) : L →ₗ[K] L where
  toFun := fun x => ⁅x, y⁆
  map_add' := by intro x z; simp [add_lie]
  map_smul' := by intro c x; simp [smul_lie]

/-- σ∘(r • _ • s) as a linear endomorphism of the tensor algebra. -/
def chiRel (e : Module.Basis ι K L) (r s : TensorAlgebra K L) : TensorAlgebra K L →ₗ[K] TensorAlgebra K L :=
  (sigmaLin e).comp ((LinearMap.mulLeft K r).comp (LinearMap.mulRight K s))

lemma chiRel_apply (e : Module.Basis ι K L) (r s t : TensorAlgebra K L) :
    chiRel e r s t = sigmaLin e (r * t * s) := by
  simp [chiRel, mul_assoc]

/-- Δ₂ : x ↦ relator (x, y), linear in x. -/
def delta2 (e : Module.Basis ι K L) (y : L) : L →ₗ[K] TensorAlgebra K L :=
  ((LinearMap.mulRight K (TensorAlgebra.ι K y)).comp (TensorAlgebra.ι K))
    - ((LinearMap.mulLeft K (TensorAlgebra.ι K y)).comp (TensorAlgebra.ι K))
    - ((TensorAlgebra.ι K).comp (brLeft y))

/-- Δ₁ : y ↦ relator (e p, y), linear in y. -/
def delta1 (e : Module.Basis ι K L) (p : ι) : L →ₗ[K] TensorAlgebra K L :=
  ((LinearMap.mulLeft K (TensorAlgebra.ι K (e p))).comp (TensorAlgebra.ι K))
    - ((LinearMap.mulRight K (TensorAlgebra.ι K (e p))).comp (TensorAlgebra.ι K))
    - ((TensorAlgebra.ι K).comp (brRight (e p)))

lemma delta1_apply (e : Module.Basis ι K L) (p : ι) (y : L) :
    delta1 e p y = TensorAlgebra.ι K (e p) * TensorAlgebra.ι K y -
      TensorAlgebra.ι K y * TensorAlgebra.ι K (e p) - TensorAlgebra.ι K ⁅e p, y⁆ := by
  simp [delta1, brRight, mul_assoc]

lemma delta2_apply (e : Module.Basis ι K L) (y : L) (x : L) :
    delta2 e y x = TensorAlgebra.ι K x * TensorAlgebra.ι K y -
      TensorAlgebra.ι K y * TensorAlgebra.ι K x - TensorAlgebra.ι K ⁅x, y⁆ := by
  simp [delta2, brLeft, mul_assoc]

end RelTests


/-- σ of a word with one extra letter inserted. -/
lemma sigmaLin_tfWord_append_one (e : Module.Basis ι K L) (u v : List ι) (k : ι) :
    sigmaLin e (tfWord e u * TensorAlgebra.ι K (e k) * tfWord e v)
      = sWord e (u ++ k :: v) := by
  have harg : tfWord e u * TensorAlgebra.ι K (e k) * tfWord e v = tfWord e (u ++ k :: v) := by
    calc
      tfWord e u * TensorAlgebra.ι K (e k) * tfWord e v
          = (tfWord e u * tfWord e [k]) * tfWord e v := by
              rw [show TensorAlgebra.ι K (e k) = tfWord e [k] by simp [tfWord]]
      _ = tfWord e ((u ++ [k]) ++ v) := by
              rw [← tfWord_append e u [k]]
              rw [← tfWord_append e (u ++ [k]) v]
      _ = tfWord e (u ++ k :: v) := by
              congr 1
              simp
  rw [harg]
  exact sigmaLin_tfWord e (u ++ k :: v)

/-- distributing a scalar-valued `Finsupp` sum across a two-sided product -/
lemma mul_finsupp_sum_mul (a : TensorAlgebra K L) (f : ι →₀ K) (x : ι → TensorAlgebra K L)
    (b : TensorAlgebra K L) :
    (a * f.sum (fun k d => d • x k)) * b =
      f.sum (fun k d => d • (a * x k * b)) := by
  calc
    (a * f.sum (fun k d => d • x k)) * b
        = (f.sum (fun k d => a * (d • x k))) * b := by
            rw [Finsupp.mul_sum]
    _ = f.sum (fun k d => (a * (d • x k)) * b) := by
            rw [Finsupp.sum_mul]
    _ = f.sum (fun k d => d • (a * x k * b)) := by
            apply Finsupp.sum_congr
            intro k hk
            rw [mul_smul_comm]
            rw [smul_mul_assoc]

/-- σ annihilates the relator on tensor words (contexts are words). -/
lemma sigmaLin_relator_word (e : Module.Basis ι K L) (u v : List ι) (i j : ι) :
    sigmaLin e (tfWord e u * taRel e i j * tfWord e v) = 0 := by
  let c : ι →₀ K := e.repr ⁅e i, e j⁆
  have hC0 : TensorAlgebra.ι K ⁅e i, e j⁆ =
      c.sum (fun k d => d • TensorAlgebra.ι K (e k)) := by
    simpa [c] using iota_bracket_expand e i j
  have hC : sigmaLin e (tfWord e u * TensorAlgebra.ι K ⁅e i, e j⁆ * tfWord e v) =
      c.sum (fun k d => d • sWord e (u ++ k :: v)) := by
    calc
      sigmaLin e (tfWord e u * TensorAlgebra.ι K ⁅e i, e j⁆ * tfWord e v)
          = sigmaLin e (tfWord e u * c.sum (fun k d => d • TensorAlgebra.ι K (e k)) * tfWord e v) := by
              rw [hC0]
      _ = sigmaLin e (c.sum (fun k d => d • (tfWord e u * TensorAlgebra.ι K (e k) * tfWord e v))) := by
              congr 1
              exact mul_finsupp_sum_mul (tfWord e u) c (fun k => TensorAlgebra.ι K (e k)) (tfWord e v)
      _ = c.sum (fun k d => d • sigmaLin e (tfWord e u * TensorAlgebra.ι K (e k) * tfWord e v)) := by
              exact map_finsupp_sum (sigmaLin e) c (fun k => tfWord e u * TensorAlgebra.ι K (e k) * tfWord e v)
      _ = c.sum (fun k d => d • sWord e (u ++ k :: v)) := by
              congr 1
              funext k d
              congr 1
              exact sigmaLin_tfWord_append_one e u v k
  have hmain : sigmaLin e (tfWord e u * taRel e i j * tfWord e v)
      = sWord e (u ++ i :: j :: v) - sWord e (u ++ j :: i :: v)
        - c.sum (fun k d => d • sWord e (u ++ k :: v)) := by
    calc
      sigmaLin e (tfWord e u * taRel e i j * tfWord e v)
          = sigmaLin e (((tfWord e u * TensorAlgebra.ι K (e i)) * TensorAlgebra.ι K (e j) * tfWord e v)
              - ((tfWord e u * TensorAlgebra.ι K (e j)) * TensorAlgebra.ι K (e i) * tfWord e v)
              - (tfWord e u * TensorAlgebra.ι K ⁅e i, e j⁆ * tfWord e v)) := by
              congr 1
              simp [taRel, mul_sub, sub_mul, mul_assoc]
      _ = sigmaLin e (((tfWord e u * TensorAlgebra.ι K (e i)) * TensorAlgebra.ι K (e j)) * tfWord e v)
            - sigmaLin e (((tfWord e u * TensorAlgebra.ι K (e j)) * TensorAlgebra.ι K (e i)) * tfWord e v)
            - sigmaLin e (tfWord e u * TensorAlgebra.ι K ⁅e i, e j⁆ * tfWord e v) := by
              simp [map_sub]
      _ = sWord e (u ++ i :: j :: v) - sWord e (u ++ j :: i :: v)
            - c.sum (fun k d => d • sWord e (u ++ k :: v)) := by
              rw [sigmaLin_tfWord_append_letter e u v i j]
              rw [sigmaLin_tfWord_append_letter e u v j i]
              rw [hC]
  rw [hmain]
  rw [sWord_swap_general e u v i j]
  abel

/-- σ annihilates the relator when the left context is a word. -/
lemma sigmaLin_relator_word_left (e : Module.Basis ι K L) (u : List ι) (i j : ι)
    (s : TensorAlgebra K L) :
    sigmaLin e (tfWord e u * taRel e i j * s) = 0 := by
  let η : TensorAlgebra K L →ₗ[K] TensorAlgebra K L :=
    { toFun := fun s => sigmaLin e (tfWord e u * taRel e i j * s)
      map_add' := by
        intro s1 s2
        simp [mul_add, map_add]
      map_smul' := by
        intro c s
        rw [mul_smul_comm]
        simp [map_smul] }
  have hηw : ∀ w : List ι, η (tfWord e w) = 0 := by
    intro w
    change sigmaLin e (tfWord e u * taRel e i j * tfWord e w) = 0
    exact sigmaLin_relator_word e u w i j
  have hz : η = 0 := by
    apply Module.Basis.ext (e.tensorAlgebra)
    intro w
    rw [← tfWord_eq_tensorAlgebra e w]
    exact hηw w
  have hs : η s = 0 := by rw [hz]; simp
  change sigmaLin e (tfWord e u * taRel e i j * s) = 0
  exact hs

/-- σ annihilates the relator with arbitrary tensor contexts (basis letters). -/
lemma sigmaLin_relator_ctx (e : Module.Basis ι K L) (i j : ι) (r s : TensorAlgebra K L) :
    sigmaLin e (r * taRel e i j * s) = 0 := by
  let ρ : TensorAlgebra K L →ₗ[K] TensorAlgebra K L :=
    { toFun := fun t => sigmaLin e (t * taRel e i j * s)
      map_add' := by
        intro t1 t2
        simp [add_mul, map_add]
      map_smul' := by
        intro c t
        rw [smul_mul_assoc]
        rw [smul_mul_assoc]
        simp [map_smul] }
  have hρw : ∀ w : List ι, ρ (tfWord e w) = 0 := by
    intro w
    change sigmaLin e (tfWord e w * taRel e i j * s) = 0
    exact sigmaLin_relator_word_left e w i j s
  have hz : ρ = 0 := by
    apply Module.Basis.ext (e.tensorAlgebra)
    intro w
    rw [← tfWord_eq_tensorAlgebra e w]
    exact hρw w
  have hr : ρ r = 0 := by rw [hz]; simp
  change sigmaLin e (r * taRel e i j * s) = 0
  exact hr

/-- σ annihilates the relator when the first Lie argument is a basis letter. -/
lemma sigmaLin_relator_basis_left (e : Module.Basis ι K L) (p : ι) (r s : TensorAlgebra K L)
    (y : L) :
    sigmaLin e (r * taRelFull (e p) y * s) = 0 := by
  let Ψ : L →ₗ[K] TensorAlgebra K L := (chiRel e r s).comp (delta1 e p)
  have hΨ : ∀ t : L, Ψ t = sigmaLin e (r * taRelFull (e p) t * s) := by
    intro t
    change (chiRel e r s) (delta1 e p t) = sigmaLin e (r * taRelFull (e p) t * s)
    rw [chiRel_apply]
    rw [delta1_apply]
    rfl
  have hb : ∀ q : ι, Ψ (e q) = 0 := by
    intro q
    rw [hΨ]
    exact sigmaLin_relator_ctx e p q r s
  have hz : Ψ = 0 := by
    apply Module.Basis.ext e
    intro q
    exact hb q
  have hy : Ψ y = 0 := by rw [hz]; simp
  rw [hΨ] at hy
  exact hy

/-- σ annihilates every relator element with arbitrary contexts. -/
lemma sigmaLin_relator_all (e : Module.Basis ι K L) :
    ∀ (x y : L) (r s : TensorAlgebra K L),
      sigmaLin e (r * (TensorAlgebra.ι K x * TensorAlgebra.ι K y -
          TensorAlgebra.ι K y * TensorAlgebra.ι K x - TensorAlgebra.ι K ⁅x, y⁆) * s) = 0 := by
  intro x y r s
  let Φ : L →ₗ[K] TensorAlgebra K L := (chiRel e r s).comp (delta2 e y)
  have hΦ : ∀ t : L, Φ t = sigmaLin e (r * taRelFull t y * s) := by
    intro t
    change (chiRel e r s) (delta2 e y t) = sigmaLin e (r * taRelFull t y * s)
    rw [chiRel_apply]
    rw [delta2_apply]
    rfl
  have hb : ∀ p : ι, Φ (e p) = 0 := by
    intro p
    rw [hΦ]
    exact sigmaLin_relator_basis_left e p r s y
  have hz : Φ = 0 := by
    apply Module.Basis.ext e
    intro p
    exact hb p
  have hx : Φ x = 0 := by rw [hz]; simp
  rw [hΦ] at hx
  change sigmaLin e (r * taRelFull x y * s) = 0
  exact hx


open TensorAlgebra
open UniversalEnvelopingAlgebra

lemma mkAlgHom_tfWord (e : Module.Basis ι K L) (w : List ι) :
    UniversalEnvelopingAlgebra.mkAlgHom K L (tfWord e w) =
      (w.map (fun i => UniversalEnvelopingAlgebra.ι K (e i))).prod := by
  induction w with
  | nil => simp [tfWord]
  | cons i w ih =>
      rw [show tfWord e (i :: w) = TensorAlgebra.ι K (e i) * tfWord e w by simp [tfWord]]
      rw [map_mul]
      rw [ih]
      rw [← UniversalEnvelopingAlgebra.ι_apply K (e i)]
      simp
end SigmaRelator

/-- Linear independence of the PBW standard monomials. -/
theorem standardMonomial_linearIndependent (K L ι : Type u) [Field K] [CharZero K]
    [LieRing L] [LieAlgebra K L] [LinearOrder ι]
    (e : Module.Basis ι K L) :
    LinearIndependent K
      (fun w : {w : List ι // w.Pairwise (fun a b : ι => a ≤ b)} =>
        (w.1.map (fun i => UniversalEnvelopingAlgebra.ι K (e i))).prod) := by
  rcases Commons.Algebra.Lie.UniversalEnveloping.linearMap_quotient_factor
      (K := K) (L := L) (M := TensorAlgebra K L) (sigmaLin e) (sigmaLin_relator_all e)
      with ⟨sigmaTilde, hsigmaTilde⟩
  let P : {w : List ι // w.Pairwise (fun a b : ι => a ≤ b)} → UniversalEnvelopingAlgebra K L :=
    fun w => (w.1.map (fun i => UniversalEnvelopingAlgebra.ι K (e i))).prod
  let Q : {w : List ι // w.Pairwise (fun a b : ι => a ≤ b)} → TensorAlgebra K L :=
    fun w => e.tensorAlgebra w.1
  have hPQ : (fun w : {w : List ι // w.Pairwise (fun a b : ι => a ≤ b)} =>
      sigmaTilde (P w)) = Q := by
    funext w
    dsimp [P, Q]
    rw [← mkAlgHom_tfWord e w.1]
    rw [hsigmaTilde]
    rw [← tfWord_eq_tensorAlgebra e w.1]
    exact sigmaLin_sorted e w.1 w.2
  have hQ : LinearIndependent K Q := by
    dsimp [Q]
    have hb := (e.tensorAlgebra).linearIndependent
    exact hb.comp Subtype.val (Subtype.val_injective)
  have hP : LinearIndependent K P := by
    have hQcomp : LinearIndependent K
        (fun w : {w : List ι // w.Pairwise (fun a b : ι => a ≤ b)} => sigmaTilde (P w)) := by
      simpa [hPQ] using hQ
    exact LinearIndependent.of_comp sigmaTilde hQcomp
  exact hP

end Commons.Algebra.Lie.PBW