import Submission.Grassmann.Assembly3

/-!
# §8 of arXiv:2209.04243, stage 4.3(ii): the re-indexing `(V₄,W₄,p) ↦ p`

`SwFinal t f d` is a sum over `(V₄,W₄)` of a sum over pairs `p = (V₃,W₃)` constrained by `Fr`.
On the `Fr`-locus the pair `(V₄,W₄)` is *determined* by `p` (`Fr_V₄W₄_unique`), and every `p`
with `V₃ ⊓ Vr = ⊥`, `W₃ ⊔ Wr = ⊤` occurs (`Fr_exists`).  Hence the whole double sum can be
re-indexed as a single sum over `p`, with the `Fr`-condition replaced by those two intrinsic
conditions on `p` (plus the order guard).

The combinatorial content is isolated in the abstract lemma `collapse_sum`, so that the proof
never has to rewrite inside the (very large) summands.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## The abstract collapsing lemma -/

/-- A constant can be pulled through a `Fintype` sum. -/
lemma ite_sum_const {α : Type*} [Fintype α] (c : Prop) [Decidable c] (F : α → ℝ) :
    (if c then ∑ a, F a else 0) = ∑ a, (if c then F a else 0) := by
  by_cases h : c <;> simp [h]

/-- **The abstract collapsing lemma.**  Suppose that for `c` satisfying `D` the relation
`R a b c` determines `(a,b)` uniquely, that `R a b c` implies `D c`, and that `R` is realised at
`(b c).1, (b c).2`.  Then the `(a,b)`-sum of the `R`-filtered sum over `c` collapses to a single
sum over `c`. -/
lemma collapse_sum {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (guard : α → β → Prop) [∀ a b, Decidable (guard a b)]
    (R : α → β → γ → Prop) [∀ a b c, Decidable (R a b c)]
    (D : γ → Prop) [DecidablePred D] (bfun : γ → α × β) (G : α → β → γ → ℝ)
    (h1 : ∀ a b c, R a b c → D c)
    (h2 : ∀ a b c, D c → R a b c → (a, b) = bfun c)
    (h3 : ∀ c, D c → R (bfun c).1 (bfun c).2 c) :
    (∑ a, ∑ b, (if guard a b then (∑ c, (if R a b c then G a b c else 0)) else 0))
      = (∑ c, (if D c then (if guard (bfun c).1 (bfun c).2 then G (bfun c).1 (bfun c).2 c
            else 0) else 0)) := by
  have key : ∀ c : γ, (∑ a, ∑ b, (if guard a b then (if R a b c then G a b c else 0) else 0))
      = (if D c then (if guard (bfun c).1 (bfun c).2 then G (bfun c).1 (bfun c).2 c
          else 0) else 0) := by
    intro c
    by_cases hD : D c
    · rw [if_pos hD]
      have hbc : R (bfun c).1 (bfun c).2 c := h3 c hD
      rw [Finset.sum_eq_single (bfun c).1]
      · rw [Finset.sum_eq_single (bfun c).2]
        · rw [if_pos hbc]
        · intro b₂ _ hb₂
          by_cases hg : guard (bfun c).1 b₂
          · rw [if_pos hg]
            rw [if_neg (c := R (bfun c).1 b₂ c)
              (fun hR => hb₂ (Prod.ext_iff.mp (h2 _ _ _ hD hR)).2)]
          · rw [if_neg hg]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro a₂ _ ha₂
        refine Finset.sum_eq_zero (fun b₂ _ => ?_)
        by_cases hg : guard a₂ b₂
        · rw [if_pos hg]
          rw [if_neg (c := R a₂ b₂ c)
            (fun hR => ha₂ (Prod.ext_iff.mp (h2 _ _ _ hD hR)).1)]
        · rw [if_neg hg]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hD]
      refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
      by_cases hg : guard a b
      · rw [if_pos hg]
        rw [if_neg (c := R a b c) (fun hR => hD (h1 a b c hR))]
      · rw [if_neg hg]
  calc (∑ a, ∑ b, (if guard a b then (∑ c, (if R a b c then G a b c else 0)) else 0))
      = (∑ a, ∑ b, ∑ c, (if guard a b then (if R a b c then G a b c else 0) else 0)) := by
        exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
          ite_sum_const (guard a b) (fun c => if R a b c then G a b c else 0)))
    _ = (∑ a, ∑ c, ∑ b, (if guard a b then (if R a b c then G a b c else 0) else 0)) := by
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = (∑ c, ∑ a, ∑ b, (if guard a b then (if R a b c then G a b c else 0) else 0)) :=
        Finset.sum_comm
    _ = (∑ c, (if D c then (if guard (bfun c).1 (bfun c).2 then G (bfun c).1 (bfun c).2 c
          else 0) else 0)) :=
        Finset.sum_congr rfl (fun c _ => key c)

/-! ## The `(V₄,W₄,p) ↦ p` re-indexing -/

/-- A pair `(V₃,W₃)` in the quotient coordinates of a triple `t`. -/
abbrev QPair (m n : ℕ) (t : Triple m n) : Type :=
  Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂) ×
    Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ t.2.1) → 𝔽₂)

/-- The `V₄` determined by `p` on the `Fr`-locus. -/
abbrev pV {m n : ℕ} (t : Triple m n) (p : QPair m n t) :
    Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t)) → 𝔽₂) :=
  Vco (VrOf t) (p.1 ⊔ VrOf t)

/-- The `W₄` determined by `p` on the `Fr`-locus. -/
abbrev pW {m n : ℕ} (t : Triple m n) (p : QPair m n t) :
    Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (WrOf t)) → 𝔽₂) :=
  Wco (WrOf t) (p.2 ⊓ WrOf t)

/-- The summand of `SwFinal` attached to `(V₄,W₄,p)`. -/
abbrev SwTerm (t : Triple m n)
    (V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ t.1) -
      Module.finrank 𝔽₂ (VrOf t)) → 𝔽₂))
    (W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (WrOf t)) → 𝔽₂)) (p : QPair m n t)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : ℝ :=
  (2 : ℝ) ^ (Module.finrank 𝔽₂ (WrOf t) *
      ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))) *
    ∑ T' : Matrix (Fin m) (Fin n) 𝔽₂,
      (l2sq (restr (Qp (liftV t.1 (liftV (VrOf t) V₄)))
          (Ip (liftW t.2.1 (liftW (WrOf t) W₄)))
          (shift T' (lapMulN (PComb t p.1 p.2) (Lsub t.1 t.2.1 f))))) ^ 2

/-- The `p`-indexed form of the switching sum. -/
def SwSumP (t : Triple m n) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (d : ℕ) : ℝ :=
  ∑ p : QPair m n t,
    (if p.1 ⊓ VrOf t = ⊥ ∧ p.2 ⊔ WrOf t = ⊤
      then (if SwGuard t d (pV t p) (pW t p) then SwTerm t (pV t p) (pW t p) p f else 0)
      else 0)

/-- The relation `R` of `collapse_sum` for the switching sum. -/
abbrev SwRel (t : Triple m n)
    (V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ t.1) -
      Module.finrank 𝔽₂ (VrOf t)) → 𝔽₂))
    (W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (WrOf t)) → 𝔽₂)) (p : QPair m n t) : Prop :=
  Fr (VrOf t) (WrOf t) (liftV (VrOf t) V₄) (liftW (WrOf t) W₄) p.1 p.2

/-- **Stage 4.3(ii)**: the `(V₄,W₄,p)`-sum of `SwFinal` is the `p`-sum of `SwSumP`. -/
theorem SwFinal_eq_SwSumP (t : Triple m n) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (d : ℕ) :
    SwFinal t f d = SwSumP t f d := by
  have h := collapse_sum (guard := SwGuard t d) (R := SwRel t)
    (D := fun p : QPair m n t => p.1 ⊓ VrOf t = ⊥ ∧ p.2 ⊔ WrOf t = ⊤)
    (bfun := fun p : QPair m n t => (pV t p, pW t p))
    (G := fun V₄ W₄ (p : QPair m n t) => SwTerm t V₄ W₄ p f)
    (fun a b c hFr => ⟨hFr.1, hFr.2.2.2.2⟩)
    (fun a b c hD hFr => Prod.ext
      ((Fr_V₄W₄_unique t a (pV t c) b (pW t c) c.1 c.2 hFr
        (Fr_exists t c.1 c.2 hD.1 hD.2)).1)
      ((Fr_V₄W₄_unique t a (pV t c) b (pW t c) c.1 c.2 hFr
        (Fr_exists t c.1 c.2 hD.1 hD.2)).2))
    (fun c hD => Fr_exists t c.1 c.2 hD.1 hD.2)
  exact h

end

end Submission.Grassmann
