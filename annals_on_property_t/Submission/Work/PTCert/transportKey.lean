import Mathlib
import Submission.Work.PTCert.fourierTransport.Common
import Submission.Work.PTCert.transportMPair
import Submission.Work.PTCert.fourierWAct

namespace Work.PTCert

open Submission.PTCert

/-- The coordinate permutation `p` as a bijection of the exponent group `(Fin m → ZMod 2)`. -/
def piPerm {m : ℕ} (p : Equiv.Perm (Fin m)) : (Fin m → ZMod 2) ≃ (Fin m → ZMod 2) where
  toFun a := fun i => a (p i)
  invFun b := fun i => b (p.symm i)
  left_inv a := by funext i; simp
  right_inv b := by funext i; simp

theorem transportKey {m : ℕ} {ι : Type} (act : (Fin m → ZMod 2) → ι → ι)
    (hact_add : ∀ a b x, act (a + b) x = act a (act b x)) (hact_zero : ∀ x, act 0 x = x)
    (M : Matrix ι ι ℝ) (hM : ∀ a x y, M (act a x) (act a y) = M x y)
    (rep : ι → ι) (nu : ι → (Fin m → ZMod 2))
    (hnu : ∀ x, act (nu x) (rep x) = x)
    (τ : ι ≃ ι) (p : Equiv.Perm (Fin m))
    (hτ : ∀ a x, τ (act a x) = act (fun i => a (p.symm i)) (τ x))
    (hMτ : ∀ x y, M (τ x) (τ y) = M x y)
    (S : Finset (Fin m)) (u v : ι) :
    Submission.PTCert.fourierW act M (S.map p.toEmbedding) (rep (τ u)) (rep (τ v)) =
      Submission.PTCert.chiS (S.map p.toEmbedding) (nu (τ u)) *
        Submission.PTCert.chiS (S.map p.toEmbedding) (nu (τ v)) *
        Submission.PTCert.fourierW act M S u v := by
  have key : (∑ a, chiS (S.map p.toEmbedding) a * M (rep (τ u)) (act a (rep (τ v))))
      = fourierW act M S (act (fun i => nu (τ u) (p i)) u)
          (act (fun i => nu (τ v) (p i)) v) := by
    rw [fourierW]
    refine Fintype.sum_equiv (piPerm p) _ _ (fun a => ?_)
    rw [chiS_map S p a, transportMPair act hact_add hact_zero M rep nu hnu τ p hτ hMτ a u v]
    rfl
  have hL : fourierW act M (S.map p.toEmbedding) (rep (τ u)) (rep (τ v))
      = chiS (S.map p.toEmbedding) (nu (τ u)) * chiS (S.map p.toEmbedding) (nu (τ v)) *
          fourierW act M S u v := by
    have hs : fourierW act M (S.map p.toEmbedding) (rep (τ u)) (rep (τ v))
        = fourierW act M S (act (fun i => nu (τ u) (p i)) u)
            (act (fun i => nu (τ v) (p i)) v) := by
      conv_lhs => rw [fourierW]
      rw [key]
    rw [hs, fourierWAct act hact_add hact_zero M hM S (fun i => nu (τ u) (p i))
      (fun i => nu (τ v) (p i)) u v, chiS_map S p (nu (τ u)), chiS_map S p (nu (τ v))]
  exact hL

end Work.PTCert
