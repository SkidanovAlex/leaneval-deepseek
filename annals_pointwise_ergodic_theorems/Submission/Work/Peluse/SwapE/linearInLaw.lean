import Mathlib
import Submission.Work.Peluse.SwapE.cubeMassRaw_shift
import Submission.Work.Peluse.SwapE.pairSum_eq
import Submission.Work.Peluse.SwapE.pairCount_eq_prod
import Submission.Work.Peluse.SwapE.cubeMassRaw_eq_zero

namespace Work.Peluse.SwapE

noncomputable section

open scoped BigOperators

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-- **`LinearInLaw`** — the box sum along the multiset slots `q₁ k[M] − q₂ k[M]` is a linear
functional of the joint law of the slot values.

Proof sketch.  Write `u k = pdir (q₁ k) (q₂ k) (h k)`, `v k = pdir (q₁ k) (q₂ k) (h' k)`,
`V = ∑ k, v k`, `n k = u k - v k`.  Then
`cornerShift u v ω = V + cornerShift n 0 ω`, so the inner `∑' x` of `pboxSum` equals
`∑' y, ∏ ω, (star^[weight ω]) (f (y + cornerShift n 0 ω)) = (S.card) * boxMass d S f n`
(translation invariance of `∑'` over `ℤ`, `Equiv.tsum_eq`).
The summand therefore depends on `(h, h')` only through `n = fun k => pdir … (h k) - pdir … (h' k)`,
and the fibres factor over `k`: `#{(h,h') : n(h,h') = n} = ∏ k, slotCount (q₁ k) (q₂ k) M (n k)`.
Group with `Finset.sum_fiberwise` (or `Finset.sum_fiberwise'`) and divide by `M^{4d}` to get
`pboxSum = ∑ n, (∏ k, slotLaw …) * boxMass …`, i.e. `lawSum` at the box `[±L]^d`.
Truncation: taking `ω = 0` and `ω = indicator {k}` in the product shows that
`boxMass d S f n = 0` as soon as `|n k| > 2N` (`SupportIn f N`), so the `n`-sum may be truncated
at any `[±L]^d` with `2N ≤ L`. -/
theorem linearInLaw : Work.Peluse.SwapE.LinearInLaw := by
  intro d q₁ q₂ M N L S f hM hf hL
  classical
  by_cases hS : S.card = 0
  · -- If `S` is empty both sides vanish: `(S.card)⁻¹ = 0` and `boxMass d S f · = 0`.
    have hS0 : ((S.card : ℂ))⁻¹ = 0 := by rw [hS]; simp
    simp [pboxSum, lawSum, boxMass, hS0]
  · -- The slot box `[±L]^d` and the image of the slot-difference map.
    set box : Finset (Fin d → ℤ) := Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) L)
      with hbox
    set Im : Finset (Fin d → ℤ) :=
      (Finset.univ : Finset ((Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M))).image
        (fun p => slotVec d q₁ q₂ M p) with hIm
    -- Step 1: the inner `∑' x` of `pboxSum` only depends on the slot-difference vector.
    have hinner : (∑ h : Fin d → Fin M × Fin M, ∑ h' : Fin d → Fin M × Fin M,
          (∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
            (f (x + cornerShift (fun k => pdir (q₁ k) (q₂ k) (h k))
                                (fun k => pdir (q₁ k) (q₂ k) (h' k)) ω))))
        = (∑ h : Fin d → Fin M × Fin M, ∑ h' : Fin d → Fin M × Fin M,
            cubeMassRaw d f (slotVec d q₁ q₂ M (h, h'))) := by
      refine Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => ?_))
      exact cubeMassRaw_shift f _ _
    have key1 : pboxSum d q₁ q₂ M S f = ((S.card : ℂ))⁻¹ * (((M : ℂ) ^ 4)⁻¹) ^ d *
        (∑ h : Fin d → Fin M × Fin M, ∑ h' : Fin d → Fin M × Fin M,
            cubeMassRaw d f (slotVec d q₁ q₂ M (h, h'))) := by
      simp only [pboxSum, hinner]
    -- Step 2: group the double sum over slot-point pairs by the slot-difference vector, then
    -- discard the vectors outside the box.
    have key2 : (∑ h : Fin d → Fin M × Fin M, ∑ h' : Fin d → Fin M × Fin M,
            cubeMassRaw d f (slotVec d q₁ q₂ M (h, h')))
        = ∑ n ∈ box,
            (∏ k : Fin d, (slotCount (q₁ k) (q₂ k) M (n k) : ℂ)) * cubeMassRaw d f n := by
      have hPS := pairSum_eq d q₁ q₂ M (cubeMassRaw d f) (box ∪ Im)
        (fun p => Finset.mem_union_right box (Finset.mem_image_of_mem _ (Finset.mem_univ p)))
      have hmiddle : (∑ n ∈ box ∪ Im, (pairCount d q₁ q₂ M n : ℂ) * cubeMassRaw d f n)
          = ∑ n ∈ box ∪ Im,
              (∏ k : Fin d, (slotCount (q₁ k) (q₂ k) M (n k) : ℂ)) * cubeMassRaw d f n := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [pairCount_eq_prod]
        push_cast
        ring
      have htr : (∑ n ∈ box ∪ Im,
              (∏ k : Fin d, (slotCount (q₁ k) (q₂ k) M (n k) : ℂ)) * cubeMassRaw d f n)
          = ∑ n ∈ box,
              (∏ k : Fin d, (slotCount (q₁ k) (q₂ k) M (n k) : ℂ)) * cubeMassRaw d f n := by
        rw [← Finset.sum_subset (Finset.subset_union_left (s₁ := box) (s₂ := Im))]
        intro x hx hxbx
        have hxIm : x ∈ Im := (Finset.mem_union.mp hx).resolve_left hxbx
        have hnot : ¬ (∀ k : Fin d, x k ∈ Finset.Icc (-(L : ℤ)) (L : ℤ)) := by
          intro h
          exact hxbx (by rw [hbox]; exact Fintype.mem_piFinset.mpr h)
        obtain ⟨k, hk⟩ := not_forall.mp hnot
        have hk' : 2 * N < (x k).natAbs := by
          simp only [Finset.mem_Icc, not_and_or, not_le] at hk
          rcases hk with hk | hk
          · have h1 : -((x k) : ℤ) ≤ (((x k).natAbs : ℕ) : ℤ) := by
              have := Int.le_natAbs (a := -(x k)); simpa using this
            have h2 : (L : ℤ) < -((x k) : ℤ) := by omega
            have h3 : (L : ℤ) < (((x k).natAbs : ℕ) : ℤ) := lt_of_lt_of_le h2 h1
            have h4 : L < (x k).natAbs := by exact_mod_cast h3
            omega
          · have h1 : (x k) ≤ (((x k).natAbs : ℕ) : ℤ) := Int.le_natAbs
            have h3 : (L : ℤ) < (((x k).natAbs : ℕ) : ℤ) := lt_of_lt_of_le hk h1
            have h4 : L < (x k).natAbs := by exact_mod_cast h3
            omega
        rw [cubeMassRaw_eq_zero hf x k hk']
        ring
      rw [hPS, hmiddle, htr]
    -- Step 3: the normalisation constants and the passage from `slotCount` to `slotLaw`.
    have key3 : ((S.card : ℂ))⁻¹ * (((M : ℂ) ^ 4)⁻¹) ^ d *
          (∑ n ∈ box,
            (∏ k : Fin d, (slotCount (q₁ k) (q₂ k) M (n k) : ℂ)) * cubeMassRaw d f n)
        = lawSum d q₁ q₂ M S f L := by
      have hkey : ∀ n : Fin d → ℤ,
          (((M : ℂ) ^ 4)⁻¹) ^ d * (∏ k : Fin d, (slotCount (q₁ k) (q₂ k) M (n k) : ℂ))
            = ∏ k : Fin d, ((slotLaw (q₁ k) (q₂ k) M (n k) : ℝ) : ℂ) := by
        intro n
        have h1 : ∀ k : Fin d, ((slotLaw (q₁ k) (q₂ k) M (n k) : ℝ) : ℂ)
            = (slotCount (q₁ k) (q₂ k) M (n k) : ℂ) * (((M : ℂ) ^ 4)⁻¹) := by
          intro k
          simp only [slotLaw]
          push_cast
          ring
        rw [Finset.prod_congr rfl (fun k _ => h1 k)]
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        simp only [Finset.card_univ, Fintype.card_fin]
        ring
      simp only [lawSum, boxMass]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      calc ((S.card : ℂ))⁻¹ * (((M : ℂ) ^ 4)⁻¹) ^ d
            * ((∏ k : Fin d, (slotCount (q₁ k) (q₂ k) M (n k) : ℂ)) * cubeMassRaw d f n)
          = ((S.card : ℂ))⁻¹ * ((((M : ℂ) ^ 4)⁻¹) ^ d
              * (∏ k : Fin d, (slotCount (q₁ k) (q₂ k) M (n k) : ℂ))) * cubeMassRaw d f n := by
            ring
        _ = ((S.card : ℂ))⁻¹
              * (∏ k : Fin d, ((slotLaw (q₁ k) (q₂ k) M (n k) : ℝ) : ℂ)) * cubeMassRaw d f n := by
            rw [hkey n]
        _ = (∏ k : Fin d, ((slotLaw (q₁ k) (q₂ k) M (n k) : ℝ) : ℂ))
              * (((S.card : ℂ))⁻¹ * cubeMassRaw d f n) := by
            ring
    calc pboxSum d q₁ q₂ M S f
        = ((S.card : ℂ))⁻¹ * (((M : ℂ) ^ 4)⁻¹) ^ d *
            (∑ h : Fin d → Fin M × Fin M, ∑ h' : Fin d → Fin M × Fin M,
              cubeMassRaw d f (slotVec d q₁ q₂ M (h, h'))) := key1
      _ = ((S.card : ℂ))⁻¹ * (((M : ℂ) ^ 4)⁻¹) ^ d *
            (∑ n ∈ box, (∏ k : Fin d, (slotCount (q₁ k) (q₂ k) M (n k) : ℂ))
              * cubeMassRaw d f n) := by rw [key2]
      _ = lawSum d q₁ q₂ M S f L := key3

end

end Work.Peluse.SwapE
