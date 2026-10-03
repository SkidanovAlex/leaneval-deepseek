/-
# `Work.FIArea6Hecke.R2.GsParseval`

The **Parseval identity for the Gauss sums** `Gs M chi S a` over a complete residue system `S`:
`∑_a |Gs a|² = |S| · ∑_s |chi s|²`.  It is the orthogonality of the additive characters on the
classes mod `M` (`GsOrth`), applied after the symmetry `ekern M (M * star a) y = ekern M (M * star y) a`
(`EkernSwap`).

No hypothesis on `S.card` is needed: the constant `|S|` is exactly the cardinality of the residue
system.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R2.Defs
import Submission.Work.FIArea6Hecke.CGD.EkernSwap
import Submission.Work.FIArea6Hecke.CGD.GsOrth
import Submission.Work.FIArea6Hecke.CGD.CrsCalculus

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R2

open scoped BigOperators
open Work.FIArea6Hecke.R

noncomputable section

lemma star_finset_sum' {ι : Type*} (T : Finset ι) (g : ι → ℂ) :
    star (∑ s ∈ T, g s) = ∑ s ∈ T, star (g s) :=
  map_sum (starRingEnd ℂ) g T

/-- **Parseval** for the conductor Gauss sums over a complete residue system. -/
theorem Gs_parseval (M : GaussianInt) (hM : M ≠ 0)
    (S : Finset GaussianInt) (hS : IsCRS M S)
    (chi : GaussianInt → ℂ) (hchi : IsCharModStrict M chi) :
    ∑ a ∈ S, Gs M chi S a * star (Gs M chi S a)
      = ((S.card : ℕ) : ℂ) * ∑ s ∈ S, chi s * star (chi s) := by
  classical
  have hexp : ∀ a : GaussianInt, Gs M chi S a * star (Gs M chi S a)
      = ∑ s ∈ S, ∑ t ∈ S, (chi s * star (chi t)) * ekern M (M * star a) (s - t) := by
    intro a
    simp only [Gs]
    rw [star_finset_sum', Finset.sum_mul]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have h1 : (chi s * ekern M (M * star a) s) * star (chi t * ekern M (M * star a) t)
        = (chi s * star (chi t))
          * (ekern M (M * star a) s * star (ekern M (M * star a) t)) := by
      rw [star_mul]; ring
    rw [h1, ekern_sub]
  calc ∑ a ∈ S, Gs M chi S a * star (Gs M chi S a)
      = ∑ a ∈ S, ∑ s ∈ S, ∑ t ∈ S,
          (chi s * star (chi t)) * ekern M (M * star a) (s - t) :=
        Finset.sum_congr rfl (fun a _ => hexp a)
    _ = ∑ s ∈ S, ∑ t ∈ S, ∑ a ∈ S,
          (chi s * star (chi t)) * ekern M (M * star a) (s - t) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ s ∈ S, ∑ t ∈ S, ∑ a ∈ S,
          (chi s * star (chi t)) * ekern M (M * star (s - t)) a := by
        refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => ?_))
        exact Finset.sum_congr rfl (fun a _ => by rw [Work.FIArea6Hecke.CGD.EkernSwap])
    _ = ∑ s ∈ S, ∑ t ∈ S,
          (chi s * star (chi t)) * (if M ∣ s - t then ((S.card : ℕ) : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => ?_))
        rw [← Finset.mul_sum]
        congr 1
        by_cases hd : M ∣ s - t
        · rw [(Work.FIArea6Hecke.CGD.GsOrth M hM S hS (s - t)).1 hd, if_pos hd]
        · rw [(Work.FIArea6Hecke.CGD.GsOrth M hM S hS (s - t)).2 hd, if_neg hd]
    _ = ∑ s ∈ S, (chi s * star (chi s)) * ((S.card : ℕ) : ℂ) := by
        refine Finset.sum_congr rfl (fun s hs => ?_)
        have hside : ∀ t ∈ S, t ≠ s →
            (chi s * star (chi t)) * (if M ∣ s - t then ((S.card : ℕ) : ℂ) else 0) = 0 := by
          intro t ht hts
          rw [if_neg (fun hd =>
            hts (Work.FIArea6Hecke.CGD.eq_of_mem_of_dvd M S hS hs ht hd).symm), mul_zero]
        rw [Finset.sum_eq_single_of_mem s hs hside, sub_self, if_pos (dvd_zero M)]
    _ = ((S.card : ℕ) : ℂ) * ∑ s ∈ S, chi s * star (chi s) := by
        rw [← Finset.sum_mul, mul_comm]

end

end Work.FIArea6Hecke.R2
