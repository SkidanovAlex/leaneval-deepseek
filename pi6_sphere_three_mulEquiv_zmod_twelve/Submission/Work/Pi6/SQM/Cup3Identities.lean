import Mathlib
import Submission.Work.Pi6.SQM.SqmValLemmas
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-! # Interval-map identities and expansions for the `∪₃` coboundary formula

The combinatorial core of `Submission/Work/Pi6/SQM/cup3Coboundary.lean`:

* the *LHS reindexing* identities `reg1u/v … reg5u/v` (the five regimes of the deleted vertex);
* the *cluster move* identities `B1, B2i … B8iii` (the movable half of the pairing);
* the *immovable* identities `C1u/v, C2, C3, C4u/v, C5, C6u/v` (matched with `T1 ⊔ T2`);
* the expansions `lhs_expand`, `t1_expand`, `t2_expand`, `t3_expand`, `t4_expand`;
* `genEval_cochainDiff'` (the sign-free face sum in `𝔽₂`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff)

macro "imap" : tactic => `(tactic|
  (refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
   simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, cup3U_val, cup3V_val, cup2U_val,
     cup2V_val, Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
   split_ifs <;> omega))


variable {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)

theorem B1 (a' b c : ℕ) (h1 : 1 ≤ b) (h2 : b + 2 ≤ m) (h3 : 1 ≤ c)
    (h4 : a' + c + 3 ≤ n + 1) (h5 : a' + c + 2 ≤ n) :
    (SimplexCategory.δ (⟨a'+1, by omega⟩ : Fin (n+2)) ≫
        (cup3U (n+1) m (a'+1) b c (by omega) h2 h3 (by omega) ≫ sh3 n m hn hm)
      = cup3U n (m+1) a' (b+1) c (by omega) (by omega) (by omega) h5 ≫ sh4 n m hn hm) ∧
    (cup3V (n+1) m (a'+1) b c (by omega) h2 h3 (by omega) ≫ sh3 n m hn hm
      = SimplexCategory.δ (⟨0, by omega⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) a' (b+1) c (by omega) (by omega) (by omega) h5 ≫ sh4 n m hn hm)) := by
  constructor <;> imap

/-- (B2i) T3 (a, b, c'+1) i=2 ↔ T4 (a, b+1, c') i=2 -/

theorem B2i (a b c' : ℕ) (h1 : 1 ≤ b) (h2 : b + 2 ≤ m) (h3 : 1 ≤ c')
    (h4 : a + c' + 3 ≤ n + 1) (h5 : a + c' + 2 ≤ n) :
    (SimplexCategory.δ (⟨a+1, by omega⟩ : Fin (n+2)) ≫
        (cup3U (n+1) m a b (c'+1) (by omega) h2 (by omega) h4 ≫ sh3 n m hn hm)
      = cup3U n (m+1) a (b+1) c' (by omega) (by omega) (by omega) h5 ≫ sh4 n m hn hm) ∧
    (cup3V (n+1) m a b (c'+1) (by omega) h2 (by omega) h4 ≫ sh3 n m hn hm
      = SimplexCategory.δ (⟨b+1, by omega⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) a (b+1) c' (by omega) (by omega) (by omega) h5 ≫ sh4 n m hn hm)) := by
  constructor <;> imap

/-- (B2ii) T3 (a, b, 1) i=2 ↔ T3 (a, b+1, 1) i=3 -/

theorem B2ii (a b : ℕ) (h1 : 1 ≤ b) (hb3 : b + 3 ≤ m) (h4 : a + 3 ≤ n + 1) :
    (SimplexCategory.δ (⟨a+1, by omega⟩ : Fin (n+2)) ≫
        (cup3U (n+1) m a b 1 (by omega) (by omega) (by omega) h4 ≫ sh3 n m hn hm)
      = SimplexCategory.δ (⟨a+2, by omega⟩ : Fin (n+2)) ≫
        (cup3U (n+1) m a (b+1) 1 (by omega) (by omega) (by omega) (by omega) ≫ sh3 n m hn hm)) ∧
    (cup3V (n+1) m a b 1 (by omega) (by omega) (by omega) h4 ≫ sh3 n m hn hm
      = cup3V (n+1) m a (b+1) 1 (by omega) (by omega) (by omega) (by omega) ≫ sh3 n m hn hm) := by
  constructor <;> imap

/-- (B2iii) T3 (a, m-2, 1) i=2 ↔ T4 (a, m-1, 1) i=4 -/

theorem B2iii (hm3 : 3 ≤ m) (a : ℕ) (h4 : a + 3 ≤ n) :
    (SimplexCategory.δ (⟨a+1, by omega⟩ : Fin (n+2)) ≫
        (cup3U (n+1) m a (m-2) 1 (by omega) (by omega) (by omega) (by omega) ≫ sh3 n m hn hm)
      = cup3U n (m+1) a (m-1) 1 (by omega) (by omega) (by omega) h4 ≫ sh4 n m hn hm) ∧
    (cup3V (n+1) m a (m-2) 1 (by omega) (by omega) (by omega) (by omega) ≫ sh3 n m hn hm
      = SimplexCategory.δ (⟨m+1, by omega⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) a (m-1) 1 (by omega) (by omega) (by omega) h4 ≫ sh4 n m hn hm)) := by
  constructor <;> imap

/-- (B3i) T3 (a, b, c'+1) i=3 ↔ T4 (a, b, c') i=3 -/

theorem B4 (a b c : ℕ) (h1 : 1 ≤ b) (h2 : b + 2 ≤ m) (h3 : 1 ≤ c)
    (h4 : a + c + 2 ≤ n + 1) (h5 : a + c + 2 ≤ n) :
    (SimplexCategory.δ (⟨a+c+2, by omega⟩ : Fin (n+2)) ≫
        (cup3U (n+1) m a b c (by omega) h2 h3 h4 ≫ sh3 n m hn hm)
      = cup3U n (m+1) a b c (by omega) (by omega) h3 h5 ≫ sh4 n m hn hm) ∧
    (cup3V (n+1) m a b c (by omega) h2 h3 h4 ≫ sh3 n m hn hm
      = SimplexCategory.δ (⟨m+1, by omega⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) a b c (by omega) (by omega) h3 h5 ≫ sh4 n m hn hm)) := by
  constructor <;> imap

theorem B3i (a b c' : ℕ) (h1 : 1 ≤ b) (h2 : b + 2 ≤ m) (h3 : 1 ≤ c')
    (h4 : a + c' + 3 ≤ n + 1) (h5 : a + c' + 2 ≤ n) :
    (SimplexCategory.δ (⟨a+c'+2, by omega⟩ : Fin (n+2)) ≫
        (cup3U (n+1) m a b (c'+1) (by omega) h2 (by omega) h4 ≫ sh3 n m hn hm)
      = cup3U n (m+1) a b c' (by omega) (by omega) (by omega) h5 ≫ sh4 n m hn hm) ∧
    (cup3V (n+1) m a b (c'+1) (by omega) h2 (by omega) h4 ≫ sh3 n m hn hm
      = SimplexCategory.δ (⟨b+1, by omega⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) a b c' (by omega) (by omega) (by omega) h5 ≫ sh4 n m hn hm)) := by
  constructor <;> imap

theorem C1u (b c : ℕ) (h1 : 1 ≤ b) (h2 : b + 2 ≤ m) (h3 : 1 ≤ c) (h4 : 0 + c + 2 ≤ n + 1)
    (h5 : 0 < n + 2) (h6 : c + 1 ≤ n) (h7 : b + 2 ≤ m) :
    SimplexCategory.δ (⟨0, h5⟩ : Fin (n+2)) ≫
        (cup3U (n+1) m 0 b c h1 h2 h3 h4 ≫ sh3 n m hn hm)
      = Work.Pi6.SQ.cup2V m n b c h7 h3 h6 ≫ shT2 n m hn hm := by
  imap

theorem C1v (b c : ℕ) (h1 : 1 ≤ b) (h2 : b + 2 ≤ m) (h3 : 1 ≤ c) (h4 : 0 + c + 2 ≤ n + 1)
    (h6 : c + 1 ≤ n) (h7 : b + 2 ≤ m) :
    cup3V (n+1) m 0 b c h1 h2 h3 h4 ≫ sh3 n m hn hm
      = Work.Pi6.SQ.cup2U m n b c h7 h3 h6 ≫ shT2 n m hn hm := by
  imap

theorem C4u (a b c : ℕ) (h1 : 1 ≤ b) (h2 : b + 2 ≤ m) (h3 : 1 ≤ c) (h4 : a + c + 2 ≤ n + 1)
    (h5 : a + c + 2 < n + 2) (h6 : a + 2 ≤ n) (h7 : b + 1 ≤ m) (h8 : a + c = n - 1) :
    SimplexCategory.δ (⟨a+c+2, h5⟩ : Fin (n+2)) ≫
        (cup3U (n+1) m a b c h1 h2 h3 h4 ≫ sh3 n m hn hm)
      = Work.Pi6.SQ.cup2U n m a b h6 h1 h7 := by
  imap

theorem C4v (a b c : ℕ) (h1 : 1 ≤ b) (h2 : b + 2 ≤ m) (h3 : 1 ≤ c) (h4 : a + c + 2 ≤ n + 1) (h6 : a + 2 ≤ n)
    (h7 : b + 1 ≤ m) (h8 : a + c = n - 1) :
    cup3V (n+1) m a b c h1 h2 h3 h4 ≫ sh3 n m hn hm
      = Work.Pi6.SQ.cup2V n m a b h6 h1 h7 := by
  imap

-- C6u/C6v: T3 (n-2, m-2, 1) i=2 ↔ T1 (n-2, m-1)

theorem C6u (hn3 : 3 ≤ n) (hm3 : 3 ≤ m) :
    SimplexCategory.δ (⟨n-1, by omega⟩ : Fin (n+2)) ≫
        (cup3U (n+1) m (n-2) (m-2) 1 (by omega) (by omega) (by omega) (by omega) ≫ sh3 n m hn hm)
      = Work.Pi6.SQ.cup2U n m (n-2) (m-1) (by omega) (by omega) (by omega) := by
  imap

theorem C6v (hn3 : 3 ≤ n) (hm3 : 3 ≤ m) :
    cup3V (n+1) m (n-2) (m-2) 1 (by omega) (by omega) (by omega) (by omega) ≫ sh3 n m hn hm
      = Work.Pi6.SQ.cup2V n m (n-2) (m-1) (by omega) (by omega) (by omega) := by
  imap


section RegimeIdentities

theorem reg1u (n m a b c k : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (hb1 : 1 ≤ b) (hb2 : b + 2 ≤ m) (hc : 1 ≤ c)
    (hac : a + c + 2 ≤ n) (hk : k ≤ a) :
    cup3U n m a b c hb1 hb2 hc hac ≫ SimplexCategory.δ (⟨k, by omega⟩ : Fin ((n+m-3)+2)) ≫ shL n m hn hm
      = SimplexCategory.δ (⟨k, by omega⟩ : Fin (n+2)) ≫
        cup3U (n+1) m (a+1) b c (by omega) (by omega) (by omega) (by omega) ≫ sh3 n m hn hm := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply]
  simp only [SimplexCategory.coe_δ, cup3U_val, Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
  split_ifs <;> omega

theorem reg1v (n m a b c k : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (hb1 : 1 ≤ b) (hb2 : b + 2 ≤ m) (hc : 1 ≤ c)
    (hac : a + c + 2 ≤ n) (hk : k ≤ a) :
    cup3V n m a b c hb1 hb2 hc hac ≫ SimplexCategory.δ (⟨k, by omega⟩ : Fin ((n+m-3)+2)) ≫ shL n m hn hm
      = cup3V (n+1) m (a+1) b c (by omega) (by omega) (by omega) (by omega) ≫ sh3 n m hn hm := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply]
  simp only [SimplexCategory.coe_δ, cup3V_val, Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
  split_ifs <;> omega

theorem reg2u (n m a b c k : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (hb1 : 1 ≤ b) (hb2 : b + 2 ≤ m) (hc : 1 ≤ c)
    (hac : a + c + 2 ≤ n) (hk1 : a + 1 ≤ k) (hk2 : k ≤ a + b) :
    cup3U n m a b c hb1 hb2 hc hac ≫ SimplexCategory.δ (⟨k, by omega⟩ : Fin ((n+m-3)+2)) ≫ shL n m hn hm
      = cup3U n (m+1) a (b+1) c (by omega) (by omega) (by omega) (by omega) ≫ sh4 n m hn hm := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply]
  simp only [SimplexCategory.coe_δ, cup3U_val, Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
  split_ifs <;> omega

theorem reg2v (n m a b c k : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (hb1 : 1 ≤ b) (hb2 : b + 2 ≤ m) (hc : 1 ≤ c)
    (hac : a + c + 2 ≤ n) (hk1 : a + 1 ≤ k) (hk2 : k ≤ a + b) :
    cup3V n m a b c hb1 hb2 hc hac ≫ SimplexCategory.δ (⟨k, by omega⟩ : Fin ((n+m-3)+2)) ≫ shL n m hn hm
      = SimplexCategory.δ (⟨k-a, by omega⟩ : Fin (m+2)) ≫
        cup3V n (m+1) a (b+1) c (by omega) (by omega) (by omega) (by omega) ≫ sh4 n m hn hm := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply]
  simp only [SimplexCategory.coe_δ, cup3V_val, Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
  split_ifs <;> omega

theorem reg3u (n m a b c k : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (hb1 : 1 ≤ b) (hb2 : b + 2 ≤ m) (hc : 1 ≤ c)
    (hac : a + c + 2 ≤ n) (hk1 : a + b + 1 ≤ k) (hk2 : k ≤ a + b + c) :
    cup3U n m a b c hb1 hb2 hc hac ≫ SimplexCategory.δ (⟨k, by omega⟩ : Fin ((n+m-3)+2)) ≫ shL n m hn hm
      = SimplexCategory.δ (⟨k-b+1, by omega⟩ : Fin (n+2)) ≫
        cup3U (n+1) m a b (c+1) (by omega) (by omega) (by omega) (by omega) ≫ sh3 n m hn hm := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply]
  simp only [SimplexCategory.coe_δ, cup3U_val, Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
  split_ifs <;> omega

theorem reg3v (n m a b c k : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (hb1 : 1 ≤ b) (hb2 : b + 2 ≤ m) (hc : 1 ≤ c)
    (hac : a + c + 2 ≤ n) (hk1 : a + b + 1 ≤ k) (hk2 : k ≤ a + b + c) :
    cup3V n m a b c hb1 hb2 hc hac ≫ SimplexCategory.δ (⟨k, by omega⟩ : Fin ((n+m-3)+2)) ≫ shL n m hn hm
      = cup3V (n+1) m a b (c+1) (by omega) (by omega) (by omega) (by omega) ≫ sh3 n m hn hm := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply]
  simp only [SimplexCategory.coe_δ, cup3V_val, Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
  split_ifs <;> omega

theorem reg4u (n m a b c k : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (hb1 : 1 ≤ b) (hb2 : b + 2 ≤ m) (hc : 1 ≤ c)
    (hac : a + c + 2 ≤ n) (hk1 : a + b + c + 1 ≤ k) (hk2 : k ≤ a + c + m - 1) :
    cup3U n m a b c hb1 hb2 hc hac ≫ SimplexCategory.δ (⟨k, by omega⟩ : Fin ((n+m-3)+2)) ≫ shL n m hn hm
      = cup3U n (m+1) a b c (by omega) (by omega) (by omega) (by omega) ≫ sh4 n m hn hm := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply]
  simp only [SimplexCategory.coe_δ, cup3U_val, Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
  split_ifs <;> omega

theorem reg4v (n m a b c k : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (hb1 : 1 ≤ b) (hb2 : b + 2 ≤ m) (hc : 1 ≤ c)
    (hac : a + c + 2 ≤ n) (hk1 : a + b + c + 1 ≤ k) (hk2 : k ≤ a + c + m - 1) :
    cup3V n m a b c hb1 hb2 hc hac ≫ SimplexCategory.δ (⟨k, by omega⟩ : Fin ((n+m-3)+2)) ≫ shL n m hn hm
      = SimplexCategory.δ (⟨k-a-c+1, by omega⟩ : Fin (m+2)) ≫
        cup3V n (m+1) a b c (by omega) (by omega) (by omega) (by omega) ≫ sh4 n m hn hm := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply]
  simp only [SimplexCategory.coe_δ, cup3V_val, Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
  split_ifs <;> omega

end RegimeIdentities


/-- (B3ii) -/
theorem B3ii (a b' : ℕ)
    (h1 : 1 ≤ b') (h2 : b' + 3 ≤ m) (h3 : 1 ≤ b' + 1) (h4 : b' + 1 + 2 ≤ m)
    (h5 : a + 1 + 2 ≤ n + 1) (h6 : b' + 2 ≤ m) (h7 : a + 3 ≤ n + 1)
    (h9 : a + 2 < n + 2) (h10 : a + 1 < n + 2) :
    (SimplexCategory.δ (⟨a+2, h9⟩ : Fin (n+2)) ≫
        (cup3U (n+1) m a (b'+1) 1 h3 h4 (le_refl 1) h5 ≫ sh3 n m hn hm)
      = SimplexCategory.δ (⟨a+1, h10⟩ : Fin (n+2)) ≫
        (cup3U (n+1) m a b' 1 h1 h6 (le_refl 1) h7 ≫ sh3 n m hn hm)) ∧
    (cup3V (n+1) m a (b'+1) 1 h3 h4 (le_refl 1) h5 ≫ sh3 n m hn hm
      = cup3V (n+1) m a b' 1 h1 h6 (le_refl 1) h7 ≫ sh3 n m hn hm) := by
  constructor <;> imap

/-- (B3iii) -/
theorem B3iii (a' : ℕ)
    (h1 : 1 ≤ (1:ℕ)) (h2 : 1 + 2 ≤ m) (h3 : 1 ≤ (1:ℕ)) (h4 : a' + 1 + 1 + 2 ≤ n + 1)
    (h5 : 1 ≤ (1:ℕ)) (h6 : 1 + 2 ≤ m + 1) (h7 : 1 ≤ (1:ℕ)) (h8 : a' + 1 + 2 ≤ n)
    (h9 : a' + 3 < n + 2) (h10 : 0 < m + 2) :
    (SimplexCategory.δ (⟨a'+3, h9⟩ : Fin (n+2)) ≫
        (cup3U (n+1) m (a'+1) 1 1 h1 h2 h3 h4 ≫ sh3 n m hn hm)
      = cup3U n (m+1) a' 1 1 h5 h6 h7 h8 ≫ sh4 n m hn hm) ∧
    (cup3V (n+1) m (a'+1) 1 1 h1 h2 h3 h4 ≫ sh3 n m hn hm
      = SimplexCategory.δ (⟨0, h10⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) a' 1 1 h5 h6 h7 h8 ≫ sh4 n m hn hm)) := by
  constructor <;> imap

/-- (B5iii) -/
theorem B5iii (a : ℕ)
    (h1 : 1 ≤ (1:ℕ)) (h2 : 1 + 2 ≤ m + 1) (h3 : 1 ≤ (1:ℕ)) (h4 : a + 1 + 2 ≤ n)
    (h5 : 1 ≤ (1:ℕ)) (h6 : 1 + 2 ≤ m) (h7 : 1 ≤ (1:ℕ)) (h8 : a + 1 + 1 + 2 ≤ n + 1)
    (h9 : a + 3 < n + 2) (h10 : 0 < m + 2) :
    (cup3U n (m+1) a 1 1 h1 h2 h3 h4 ≫ sh4 n m hn hm
      = SimplexCategory.δ (⟨a+3, h9⟩ : Fin (n+2)) ≫
        (cup3U (n+1) m (a+1) 1 1 h5 h6 h7 h8 ≫ sh3 n m hn hm)) ∧
    (SimplexCategory.δ (⟨0, h10⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) a 1 1 h1 h2 h3 h4 ≫ sh4 n m hn hm)
      = cup3V (n+1) m (a+1) 1 1 h5 h6 h7 h8 ≫ sh3 n m hn hm) := by
  constructor <;> imap

theorem B5ii (a c' : ℕ)
    (h1 : 1 ≤ (1:ℕ)) (h2 : 1 + 2 ≤ m + 1) (h3 : 1 ≤ c' + 1) (h4 : a + c' + 1 + 2 ≤ n)
    (h5 : 1 ≤ (1:ℕ)) (h6 : 1 + 2 ≤ m + 1) (h7 : 1 ≤ c') (h8 : a + 1 + c' + 2 ≤ n)
    (h9 : 0 < m + 2) (h10 : 1 < m + 2) :
    (cup3U n (m+1) a 1 (c'+1) h1 h2 h3 h4 ≫ sh4 n m hn hm
      = cup3U n (m+1) (a+1) 1 c' h5 h6 h7 h8 ≫ sh4 n m hn hm) ∧
    (SimplexCategory.δ (⟨0, h9⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) a 1 (c'+1) h1 h2 h3 h4 ≫ sh4 n m hn hm)
      = SimplexCategory.δ (⟨1, h10⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) (a+1) 1 c' h5 h6 h7 h8 ≫ sh4 n m hn hm)) := by
  constructor <;> imap

theorem B5i (a b c : ℕ) (h1 : 1 ≤ b) (h2 : b + 2 ≤ m + 1) (h3 : 1 ≤ c) (h4 : a + c + 2 ≤ n)
    (hb1 : 1 ≤ b - 1) (h5 : b - 1 + 2 ≤ m) (h6 : a + 1 + c + 2 ≤ n + 1) (h7 : 0 < m + 2)
    (h8 : a + 1 < n + 2) :
    (cup3U n (m+1) a b c h1 h2 h3 h4 ≫ sh4 n m hn hm
      = SimplexCategory.δ (⟨a+1, h8⟩ : Fin (n+2)) ≫
        (cup3U (n+1) m (a+1) (b-1) c hb1 h5 h3 h6 ≫ sh3 n m hn hm)) ∧
    (SimplexCategory.δ (⟨0, h7⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) a b c h1 h2 h3 h4 ≫ sh4 n m hn hm)
      = cup3V (n+1) m (a+1) (b-1) c hb1 h5 h3 h6 ≫ sh3 n m hn hm) := by
  constructor <;> imap

/-- (B6i) -/

theorem B6i (a b c : ℕ) (h1 : 1 ≤ b) (h2 : b + 2 ≤ m + 1) (h3 : 1 ≤ c) (h4 : a + c + 2 ≤ n)
    (hb1 : 1 ≤ b - 1) (h5 : b - 1 + 2 ≤ m) (h6 : a + c + 2 ≤ n + 1) (h7 : b < m + 2)
    (h8 : a + 1 < n + 2) :
    (cup3U n (m+1) a b c h1 h2 h3 h4 ≫ sh4 n m hn hm
      = SimplexCategory.δ (⟨a+1, h8⟩ : Fin (n+2)) ≫
        (cup3U (n+1) m a (b-1) (c+1) hb1 h5 (by omega) (by omega) ≫ sh3 n m hn hm)) ∧
    (SimplexCategory.δ (⟨b, h7⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) a b c h1 h2 h3 h4 ≫ sh4 n m hn hm)
      = cup3V (n+1) m a (b-1) (c+1) hb1 h5 (by omega) (by omega) ≫ sh3 n m hn hm) := by
  constructor <;> imap

/-- (B7i) -/

theorem B7i (a b c : ℕ) (h1 : 1 ≤ b) (h2 : b + 2 ≤ m + 1) (h3 : 1 ≤ c) (h4 : a + c + 2 ≤ n)
    (h5 : b + 2 ≤ m) (h6 : 1 ≤ c + 1) (h7 : a + c + 1 + 2 ≤ n + 1) (h8 : a + c + 2 < n + 2)
    (h9 : b + 1 < m + 2) :
    (cup3U n (m+1) a b c h1 h2 h3 h4 ≫ sh4 n m hn hm
      = SimplexCategory.δ (⟨a+c+2, h8⟩ : Fin (n+2)) ≫
        (cup3U (n+1) m a b (c+1) h1 h5 h6 h7 ≫ sh3 n m hn hm)) ∧
    (SimplexCategory.δ (⟨b+1, h9⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) a b c h1 h2 h3 h4 ≫ sh4 n m hn hm)
      = cup3V (n+1) m a b (c+1) h1 h5 h6 h7 ≫ sh3 n m hn hm) := by
  constructor <;> imap

/-- (B7ii) -/

theorem B7ii (a c : ℕ) (h1 : 1 ≤ m - 1) (h2 : m - 1 + 2 ≤ m + 1) (h3 : 1 ≤ c)
    (h4 : a + c + 2 ≤ n) (h6 : 1 ≤ c + 1) (h7 : a + c + 1 + 2 ≤ n) (h8 : m < m + 2)
    (h9 : m + 1 < m + 2) :
    (cup3U n (m+1) a (m-1) c h1 h2 h3 h4 ≫ sh4 n m hn hm
      = cup3U n (m+1) a (m-1) (c+1) h1 h2 h6 h7 ≫ sh4 n m hn hm) ∧
    (SimplexCategory.δ (⟨m, h8⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) a (m-1) c h1 h2 h3 h4 ≫ sh4 n m hn hm)
      = SimplexCategory.δ (⟨m+1, h9⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) a (m-1) (c+1) h1 h2 h6 h7 ≫ sh4 n m hn hm)) := by
  constructor <;> imap

theorem B8i (a b c : ℕ) (h1 : 1 ≤ b) (h2 : b + 2 ≤ m) (h3 : 1 ≤ c) (h4 : a + c + 2 ≤ n)
    (h5 : m + 1 < m + 2) (h6 : a + c + 2 < n + 2) :
    (cup3U n (m+1) a b c h1 (by omega) h3 h4 ≫ sh4 n m hn hm
      = SimplexCategory.δ (⟨a+c+2, h6⟩ : Fin (n+2)) ≫
        (cup3U (n+1) m a b c h1 h2 h3 (by omega) ≫ sh3 n m hn hm)) ∧
    (SimplexCategory.δ (⟨m+1, h5⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) a b c h1 (by omega) h3 h4 ≫ sh4 n m hn hm)
      = cup3V (n+1) m a b c h1 h2 h3 (by omega) ≫ sh3 n m hn hm) := by
  constructor <;> imap

/-- (B8iii) T4 (a,m-1,1) i=4 ↔ T3 (a,m-2,1) i=2 -/

theorem B8iii (hm3 : 3 ≤ m) (a : ℕ) (h1 : 1 ≤ m - 1) (h2 : m - 1 + 2 ≤ m + 1) (h3 : 1 ≤ (1:ℕ))
    (h4 : a + 1 + 2 ≤ n) (h5 : 1 ≤ m - 2) (h6 : m - 2 + 2 ≤ m) (h7 : a + 1 + 2 ≤ n + 1)
    (h8 : a + 1 < n + 2) (h9 : m + 1 < m + 2) :
    (cup3U n (m+1) a (m-1) 1 h1 h2 h3 h4 ≫ sh4 n m hn hm
      = SimplexCategory.δ (⟨a+1, h8⟩ : Fin (n+2)) ≫
        (cup3U (n+1) m a (m-2) 1 h5 h6 h3 h7 ≫ sh3 n m hn hm)) ∧
    (SimplexCategory.δ (⟨m+1, h9⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) a (m-1) 1 h1 h2 h3 h4 ≫ sh4 n m hn hm)
      = cup3V (n+1) m a (m-2) 1 h5 h6 h3 h7 ≫ sh3 n m hn hm) := by
  constructor <;> imap

/-- (C2) T3 (0,1,1) i=3 ↔ T2 (0,1) -/

theorem C2 (hm3 : 3 ≤ m) (h8 : 2 < n + 2) :
    (SimplexCategory.δ (⟨2, h8⟩ : Fin (n+2)) ≫
        (cup3U (n+1) m 0 1 1 (by omega) (by omega) (by omega) (by omega) ≫ sh3 n m hn hm)
      = Work.Pi6.SQ.cup2V m n 0 1 (by omega) (by omega) (by omega) ≫ shT2 n m hn hm) ∧
    (cup3V (n+1) m 0 1 1 (by omega) (by omega) (by omega) (by omega) ≫ sh3 n m hn hm
      = Work.Pi6.SQ.cup2U m n 0 1 (by omega) (by omega) (by omega) ≫ shT2 n m hn hm) := by
  constructor <;> imap

/-- (C3) T4 (0,1,c) i=2 ↔ T2 (0,c+1) -/

theorem C3 (c : ℕ) (h1 : 1 ≤ (1:ℕ)) (h2 : 1 + 2 ≤ m + 1) (h3 : 1 ≤ c) (h4 : 0 + c + 2 ≤ n)
    (h5 : 1 < m + 2) (h6 : 2 ≤ m) (h7 : 1 ≤ c + 1) (h8 : c + 1 + 1 ≤ n) :
    (cup3U n (m+1) 0 1 c h1 h2 h3 h4 ≫ sh4 n m hn hm
      = Work.Pi6.SQ.cup2V m n 0 (c+1) h6 h7 h8 ≫ shT2 n m hn hm) ∧
    (SimplexCategory.δ (⟨1, h5⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) 0 1 c h1 h2 h3 h4 ≫ sh4 n m hn hm)
      = Work.Pi6.SQ.cup2U m n 0 (c+1) h6 h7 h8 ≫ shT2 n m hn hm) := by
  constructor <;> imap

/-- (C5) T4 (a,m-1,c) i=3 ↔ T1 (a,m-1) (a + c = n - 2) -/

theorem C5 (a c : ℕ) (h1 : 1 ≤ m - 1) (h2 : m - 1 + 2 ≤ m + 1) (h3 : 1 ≤ c)
    (h4 : a + c + 2 ≤ n) (h5 : a + 2 ≤ n) (h7 : m - 1 + 1 ≤ m) (h6 : m < m + 2)
    (h8 : a + c = n - 2) :
    (cup3U n (m+1) a (m-1) c h1 h2 h3 h4 ≫ sh4 n m hn hm
      = Work.Pi6.SQ.cup2U n m a (m-1) h5 h1 h7) ∧
    (SimplexCategory.δ (⟨m, h6⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) a (m-1) c h1 h2 h3 h4 ≫ sh4 n m hn hm)
      = Work.Pi6.SQ.cup2V n m a (m-1) h5 h1 h7) := by
  constructor <;> imap

theorem reg5u (n m a b c k : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (hb1 : 1 ≤ b) (hb2 : b + 2 ≤ m)
    (hc : 1 ≤ c) (hac : a + c + 2 ≤ n) (hk1 : a + c + m ≤ k) (hk2 : k ≤ n + m - 2)
    (h5 : k < (n+m-3)+2) (h6 : k - m + 3 < n + 2) :
    Work.Pi6.SQM.cup3U n m a b c hb1 hb2 hc hac ≫
        SimplexCategory.δ (⟨k, h5⟩ : Fin ((n+m-3)+2)) ≫ shL n m hn hm
      = SimplexCategory.δ (⟨k-m+3, h6⟩ : Fin (n+2)) ≫
        (Work.Pi6.SQM.cup3U (n+1) m a b c (by omega) hb2 hc (by omega) ≫ sh3 n m hn hm) := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
  simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, Work.Pi6.SQM.cup3U_val,
    Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
  split_ifs <;> omega

theorem reg5v (n m a b c k : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (hb1 : 1 ≤ b) (hb2 : b + 2 ≤ m)
    (hc : 1 ≤ c) (hac : a + c + 2 ≤ n) (hk1 : a + c + m ≤ k) (hk2 : k ≤ n + m - 2)
    (h5 : k < (n+m-3)+2) :
    Work.Pi6.SQM.cup3V n m a b c hb1 hb2 hc hac ≫
        SimplexCategory.δ (⟨k, h5⟩ : Fin ((n+m-3)+2)) ≫ shL n m hn hm
      = Work.Pi6.SQM.cup3V (n+1) m a b c (by omega) hb2 hc (by omega) ≫ sh3 n m hn hm := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
  simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, Work.Pi6.SQM.cup3V_val,
    Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
  split_ifs <;> omega

lemma genEval_cochainDiff' {X : SSet} {k : ℕ} (γ : Cochain F2 X k) (τ : X _⦋k+1⦌) :
    genEval F2 X (cochainDiff F2 X γ) τ = ∑ i : Fin (k+2), genEval F2 X γ (X.δ i τ) := by
  rw [Work.Cohomology.genEval_cochainDiff]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hone : (-1 : F2) = 1 := by decide
  rw [hone, one_pow, one_mul]

/-- Expansion of the LHS: `δ(u∪₃v)` evaluated at `σ` is a four-fold sum over the deleted vertex `k`
and the `∪₃`-configuration `(a,b,c)` of the deleted simplex. -/
theorem lhs_expand (X : SSet) (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m)
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hcast : (n+m-3)+1 = n+m-2) (σ : X _⦋n+m-2⦌) :
    genEval F2 X (hcast ▸ cochainDiff F2 X (cup3 X n m u v)) σ
      = ∑ k : Fin ((n+m-3)+2), ∑ a : Fin (n-2), ∑ b : Fin (m-2), ∑ c : Fin (n-2),
          (if h : a.val + c.val + 3 ≤ n then
            genEval F2 X u (X.map ((cup3U n m a.val (b.val+1) (c.val+1) (by omega) (by omega)
                (by omega) (by omega)) ≫
                SimplexCategory.δ (⟨k.val, by omega⟩ : Fin ((n+m-3)+2)) ≫ shL n m hn hm).op σ) *
            genEval F2 X v (X.map ((cup3V n m a.val (b.val+1) (c.val+1) (by omega) (by omega)
                (by omega) (by omega)) ≫
                SimplexCategory.δ (⟨k.val, by omega⟩ : Fin ((n+m-3)+2)) ≫ shL n m hn hm).op σ)
          else 0) := by
  rw [Work.Cohomology.genEval_cast]
  rw [genEval_cochainDiff' (X := X) (γ := cup3 X n m u v)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [genEval_cup3]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  by_cases h : a.val + c.val + 3 ≤ n
  · rw [dif_pos h, dif_pos h]
    congr 1
    · rw [SimplicialObject.δ_def, Work.Cohomology.mop, Work.Cohomology.mop]
      rfl
    · rw [SimplicialObject.δ_def, Work.Cohomology.mop, Work.Cohomology.mop]
      rfl
  · rw [dif_neg h, dif_neg h]

/-- Expansion of `T1 = u∪₂v` at `σ`. -/
theorem t1_expand (X : SSet) (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m)
    (hn : 2 ≤ n) (hm : 2 ≤ m) (σ : X _⦋n+m-2⦌) :
    genEval F2 X (Work.Pi6.SQ.cup2 X n m u v) σ
      = ∑ a : Fin (n-1), ∑ b : Fin (m-1),
          genEval F2 X u (X.map (Work.Pi6.SQ.cup2U n m a.val (b.val+1) (by omega) (by omega)
              (by omega)).op σ) *
          genEval F2 X v (X.map (Work.Pi6.SQ.cup2V n m a.val (b.val+1) (by omega) (by omega)
              (by omega)).op σ) := by
  rw [Work.Pi6.SQ.genEval_cup2]

theorem t2_expand (X : SSet) (n m : ℕ) (v : Cochain F2 X m) (u : Cochain F2 X n)
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hcast : m + n - 2 = n + m - 2) (σ : X _⦋n+m-2⦌) :
    genEval F2 X (hcast ▸ Work.Pi6.SQ.cup2 X m n v u) σ
      = ∑ a : Fin (m-1), ∑ b : Fin (n-1),
          genEval F2 X v (X.map (Work.Pi6.SQ.cup2U m n a.val (b.val+1) (by omega) (by omega)
              (by omega) ≫ Work.Cohomology.shmap (m + n - 2) (n + m - 2) hcast).op σ) *
          genEval F2 X u (X.map (Work.Pi6.SQ.cup2V m n a.val (b.val+1) (by omega) (by omega)
              (by omega) ≫ Work.Cohomology.shmap (m + n - 2) (n + m - 2) hcast).op σ) := by
  rw [Work.Cohomology.genEval_cast, Work.Pi6.SQ.genEval_cup2]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  · rw [Work.Cohomology.mop (φ := Work.Cohomology.shmap (m + n - 2) (n + m - 2) hcast)
      (ψ := Work.Pi6.SQ.cup2U m n a.val (b.val+1) (by omega) (by omega) (by omega)) σ]
  · rw [Work.Cohomology.mop (φ := Work.Cohomology.shmap (m + n - 2) (n + m - 2) hcast)
      (ψ := Work.Pi6.SQ.cup2V m n a.val (b.val+1) (by omega) (by omega) (by omega)) σ]

theorem t3_expand (X : SSet) (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m)
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hcast : (n+1) + m - 3 = n + m - 2) (σ : X _⦋n+m-2⦌) :
    genEval F2 X (hcast ▸ cup3 X (n+1) m (cochainDiff F2 X u) v) σ
      = ∑ a : Fin (n-1), ∑ b : Fin (m-2), ∑ c : Fin (n-1),
          (if h : a.val + c.val + 3 ≤ n + 1 then
            (∑ j : Fin (n+2),
              genEval F2 X u (X.map ((SimplexCategory.δ (⟨j.val, by omega⟩ : Fin (n+2))) ≫
                  (cup3U (n+1) m a.val (b.val+1) (c.val+1) (by omega) (by omega) (by omega)
                    (by omega)) ≫ Work.Cohomology.shmap ((n+1)+m-3) (n+m-2) hcast).op σ)) *
            genEval F2 X v (X.map ((cup3V (n+1) m a.val (b.val+1) (c.val+1) (by omega) (by omega)
                (by omega) (by omega)) ≫ Work.Cohomology.shmap ((n+1)+m-3) (n+m-2) hcast).op σ)
          else 0) := by
  rw [Work.Cohomology.genEval_cast, genEval_cup3]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  by_cases h : a.val + c.val + 3 ≤ n + 1
  · rw [dif_pos h, dif_pos h]
    congr 1
    · rw [genEval_cochainDiff']
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [SimplicialObject.δ_def]
      rw [Work.Cohomology.mop (φ := cup3U (n+1) m a.val (b.val+1) (c.val+1) (by omega) (by omega)
            (by omega) (by omega))
          (ψ := SimplexCategory.δ (⟨j.val, by omega⟩ : Fin (n+2)))
          (X.map (Work.Cohomology.shmap ((n+1)+m-3) (n+m-2) hcast).op σ)]
      rw [Work.Cohomology.mop
          (φ := Work.Cohomology.shmap ((n+1)+m-3) (n+m-2) hcast)
          (ψ := (SimplexCategory.δ (⟨j.val, by omega⟩ : Fin (n+2))) ≫
            cup3U (n+1) m a.val (b.val+1) (c.val+1) (by omega) (by omega) (by omega) (by omega))
          σ]
      simp only [Category.assoc]
    · rw [Work.Cohomology.mop
          (φ := Work.Cohomology.shmap ((n+1)+m-3) (n+m-2) hcast)
          (ψ := cup3V (n+1) m a.val (b.val+1) (c.val+1) (by omega) (by omega) (by omega) (by omega))
          σ]
  · rw [dif_neg h, dif_neg h]

theorem t4_expand (X : SSet) (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m)
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hcast : n + (m+1) - 3 = n + m - 2) (σ : X _⦋n+m-2⦌) :
    genEval F2 X (hcast ▸ cup3 X n (m+1) u (cochainDiff F2 X v)) σ
      = ∑ a : Fin (n-2), ∑ b : Fin (m-1), ∑ c : Fin (n-2),
          (if h : a.val + c.val + 3 ≤ n then
            genEval F2 X u (X.map ((cup3U n (m+1) a.val (b.val+1) (c.val+1) (by omega) (by omega)
                (by omega) (by omega)) ≫ Work.Cohomology.shmap (n+(m+1)-3) (n+m-2) hcast).op σ) *
            (∑ j : Fin (m+2),
              genEval F2 X v (X.map ((SimplexCategory.δ (⟨j.val, by omega⟩ : Fin (m+2))) ≫
                  (cup3V n (m+1) a.val (b.val+1) (c.val+1) (by omega) (by omega) (by omega)
                    (by omega)) ≫ Work.Cohomology.shmap (n+(m+1)-3) (n+m-2) hcast).op σ))
          else 0) := by
  rw [Work.Cohomology.genEval_cast (h := hcast)]
  rw [genEval_cup3]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  by_cases h : a.val + c.val + 3 ≤ n
  · rw [dif_pos h, dif_pos h]
    congr 1
    · rw [Work.Cohomology.mop
          (φ := Work.Cohomology.shmap (n+(m+1)-3) (n+m-2) hcast)
          (ψ := cup3U n (m+1) a.val (b.val+1) (c.val+1) (by omega) (by omega) (by omega) (by omega))
          σ]
    · rw [genEval_cochainDiff']
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [SimplicialObject.δ_def]
      rw [Work.Cohomology.mop (φ := cup3V n (m+1) a.val (b.val+1) (c.val+1) (by omega) (by omega)
            (by omega) (by omega))
          (ψ := SimplexCategory.δ (⟨j.val, by omega⟩ : Fin (m+2)))
          (X.map (Work.Cohomology.shmap (n+(m+1)-3) (n+m-2) hcast).op σ)]
      rw [Work.Cohomology.mop
          (φ := Work.Cohomology.shmap (n+(m+1)-3) (n+m-2) hcast)
          (ψ := (SimplexCategory.δ (⟨j.val, by omega⟩ : Fin (m+2))) ≫
            cup3V n (m+1) a.val (b.val+1) (c.val+1) (by omega) (by omega) (by omega) (by omega))
          σ]
      simp only [Category.assoc]
  · rw [dif_neg h, dif_neg h]

/-- Splitting a sum over `Fin N` into a finite set `s` and its complement. -/
lemma sum_univ_eq_sum_compl_add {N : ℕ} (s : Finset (Fin N)) (f : Fin N → F2) :
    (∑ i : Fin N, f i) = (∑ i ∈ Finset.univ \ s, f i) + ∑ i ∈ s, f i := by
  rw [← Finset.sum_sdiff (Finset.subset_univ s)]

/-- The four cut positions inside the `∪₃` (`T3`) `u`-simplex of parameters `(a,b,c)`:
`a`, `a+1`, `a+c+1`, `a+c+2` (see the README). -/
def cuts3 (n a c : ℕ) (h : a + c + 2 < n + 2) : Finset (Fin (n+2)) :=
  {⟨a, by omega⟩, ⟨a+1, by omega⟩, ⟨a+c+1, by omega⟩, ⟨a+c+2, h⟩}

end

end Work.Pi6.SQM
