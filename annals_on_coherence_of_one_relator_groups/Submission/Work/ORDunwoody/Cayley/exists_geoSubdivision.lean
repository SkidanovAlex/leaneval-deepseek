import Mathlib
import Submission.Work.ORDunwoody.Cayley.Basic
import Submission.Work.ORDunwoody.Cayley.smul_rev_path
import Submission.Work.ORDunwoody.Basic
import Submission.Work.ORDunwoody.Foundations.Cayley

universe u

namespace Work.ORDunwoody.Cayley

open Work.ORDunwoody

/-- Arithmetic of the reversal of `Fin (n+1)`. -/
private lemma val_add_val_rev {n : ℕ} (i : Fin (n + 1)) : (i : ℕ) + (Fin.rev i : ℕ) = n := by
  rw [Fin.val_rev]
  omega

/-- Arithmetic of the reversal of `Fin (n+1)`, addends swapped. -/
private lemma val_rev_add_val {n : ℕ} (i : Fin (n + 1)) : (Fin.rev i : ℕ) + (i : ℕ) = n := by
  rw [Fin.val_rev]
  omega

-- A path in a tree, reversed and translated by a group element, is again a path:
-- this is `Work.ORDunwoody.Cayley.smul_rev_path`, proved in
-- `Submission.Work.ORDunwoody.Cayley.smul_rev_path` and imported below.

theorem exists_geoSubdivision {G : Type u} [Group G] {V : Type u} [MulAction G V]
    (T : Work.ORDunwoody.GTree G V) (t₀ : V) (P : Work.ORDunwoody.FinPresentation G) :
    ∃ (L : Fin P.n × Bool → ℕ) (geo : (x : Fin P.n × Bool) → Fin (L x + 1) → V),
      (∀ x, geo x 0 = t₀) ∧
      (∀ x, geo x (Fin.last (L x)) = Work.ORDunwoody.Cayley.CayV.genE P x • t₀) ∧
      (∀ (x : Fin P.n × Bool) (i : Fin (L x)),
        T.Adj (geo x i.castSucc) (geo x i.succ)) ∧
      (∀ x, Function.Injective (geo x)) ∧
      (∀ x, L (Work.ORDunwoody.Cayley.swapLetter x) = L x) ∧
      (∀ (x : Fin P.n × Bool) (i : Fin (L x + 1)),
        ∃ j : Fin (L (Work.ORDunwoody.Cayley.swapLetter x) + 1),
          (i : ℕ) + (j : ℕ) = L x ∧
            Work.ORDunwoody.Cayley.CayV.genE P x •
                geo (Work.ORDunwoody.Cayley.swapLetter x) j = geo x i) ∧
      (∀ (x : Fin P.n × Bool) (j : Fin (L (Work.ORDunwoody.Cayley.swapLetter x) + 1)),
        ∃ i : Fin (L x + 1),
          (i : ℕ) + (j : ℕ) = L x ∧
            Work.ORDunwoody.Cayley.CayV.genE P x •
                geo (Work.ORDunwoody.Cayley.swapLetter x) j = geo x i) := by
  classical
  have hpath : ∀ i : Fin P.n, ∃ (M : ℕ) (p : Fin (M + 1) → V),
      p 0 = t₀ ∧ p (Fin.last M) = CayV.genE P (i, true) • t₀ ∧
        (∀ k : Fin M, T.Adj (p k.castSucc) (p k.succ)) ∧ Function.Injective p :=
    fun i => Work.ORDunwoody.exists_Tgeodesic T t₀ (CayV.genE P (i, true) • t₀)
  choose M v hv using hpath
  have hv0 : ∀ i, v i 0 = t₀ := fun i => (hv i).1
  have hvlast : ∀ i, v i (Fin.last (M i)) = CayV.genE P (i, true) • t₀ := fun i => (hv i).2.1
  have hvadj : ∀ i (k : Fin (M i)), T.Adj (v i k.castSucc) (v i k.succ) :=
    fun i => (hv i).2.2.1
  have hvinj : ∀ i, Function.Injective (v i) := fun i => (hv i).2.2.2
  let L : Fin P.n × Bool → ℕ := fun x => M x.1
  let geo : (x : Fin P.n × Bool) → Fin (L x + 1) → V :=
    fun x j => if x.2 then v x.1 j else (CayV.genE P (x.1, true))⁻¹ • v x.1 (Fin.rev j)
  have hswap : ∀ (i : Fin P.n), CayV.genE P (i, false) = (CayV.genE P (i, true))⁻¹ :=
    fun i => CayV.genE_swap P (i, true)
  have hLs : ∀ x, L (swapLetter x) = L x := fun x => rfl
  refine ⟨L, geo, ?_, ?_, ?_, ?_, hLs, ?_, ?_⟩
  · intro x
    obtain ⟨i, b⟩ := x
    cases b
    · show (CayV.genE P (i, true))⁻¹ • v i ((0 : Fin (M i + 1)).rev) = t₀
      rw [Fin.rev_zero (M i), hvlast i]
      exact inv_smul_smul _ _
    · exact hv0 i
  · intro x
    obtain ⟨i, b⟩ := x
    cases b
    · show (CayV.genE P (i, true))⁻¹ • v i ((Fin.last (M i)).rev) = CayV.genE P (i, false) • t₀
      rw [Fin.rev_last (M i), hv0 i, hswap i]
    · exact hvlast i
  · intro x k
    obtain ⟨i, b⟩ := x
    cases b
    · exact (smul_rev_path (T := T) (g := (CayV.genE P (i, true))⁻¹) (w := v i)
        (hvadj i) (hvinj i)).1 k
    · exact hvadj i k
  · intro x
    obtain ⟨i, b⟩ := x
    cases b
    · exact (smul_rev_path (T := T) (g := (CayV.genE P (i, true))⁻¹) (w := v i)
        (hvadj i) (hvinj i)).2
    · exact hvinj i
  · intro x r
    refine ⟨Fin.rev r, val_add_val_rev r, ?_⟩
    obtain ⟨i, b⟩ := x
    cases b
    · show CayV.genE P (i, false) • v i (@Fin.rev (M i + 1) r)
          = (CayV.genE P (i, true))⁻¹ • v i (@Fin.rev (M i + 1) r)
      rw [hswap i]
    · show CayV.genE P (i, true) •
            ((CayV.genE P (i, true))⁻¹ • v i (@Fin.rev (M i + 1) (@Fin.rev (M i + 1) r)))
          = v i r
      rw [Fin.rev_rev, smul_inv_smul]
  · intro x r
    refine ⟨Fin.rev r, val_rev_add_val r, ?_⟩
    obtain ⟨i, b⟩ := x
    cases b
    · show CayV.genE P (i, false) • v i r
          = (CayV.genE P (i, true))⁻¹ • v i (@Fin.rev (M i + 1) (@Fin.rev (M i + 1) r))
      rw [hswap i]
      exact congrArg (fun y => (CayV.genE P (i, true))⁻¹ • y)
        (congrArg (v i) (Fin.rev_rev r)).symm
    · show CayV.genE P (i, true) • ((CayV.genE P (i, true))⁻¹ • v i (@Fin.rev (M i + 1) r))
          = v i (@Fin.rev (M i + 1) r)
      rw [smul_inv_smul]

end Work.ORDunwoody.Cayley
