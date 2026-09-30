import Mathlib
import Submission.Work.BW.LiouvilleAux.sum_mult_erase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem est15_bracket {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    (v₀ : NumberField.InfinitePlace K) [DecidableEq (NumberField.InfinitePlace K)]
    (X : K) (p : ι → K) (hX : X ≠ 0) (hp : p ≠ 0)
    (Binf : ℝ) (Bfin : NumberField.FinitePlace K → ℝ)
    (M : NumberField.InfinitePlace K → ℝ) (Mf : NumberField.FinitePlace K → ℝ)
    (hBfin_supp : Function.HasFiniteSupport Bfin) (hMf_supp : Function.HasFiniteSupport Mf)
    (hh : (∑ w : NumberField.InfinitePlace K, ((w.mult : ℕ) : ℝ) * Real.log (⨆ i, w (p i)))
            + (∑ᶠ w : NumberField.FinitePlace K, Real.log (⨆ i, w (p i))) = Height.logHeight p)
    (hinf : ∀ w ∈ Finset.univ.erase v₀, Real.log (w X)
        ≤ Real.log (⨆ i, w (p i)) + Real.log (Fintype.card ι : ℝ) + Binf + M w)
    (hfin : ∀ w : NumberField.FinitePlace K, Real.log (w X)
        ≤ Real.log (⨆ i, w (p i)) + Bfin w + Mf w) :
    (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * Real.log (w X))
      + (∑ᶠ w : NumberField.FinitePlace K, Real.log (w X))
    ≤ Height.logHeight p - ((v₀.mult : ℕ) : ℝ) * Real.log (⨆ i, v₀ (p i))
      + (((Module.finrank ℚ K : ℝ) - ((v₀.mult : ℕ) : ℝ)) * (Real.log (Fintype.card ι : ℝ) + Binf))
      + (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * M w)
      + (∑ᶠ w : NumberField.FinitePlace K, Mf w)
      + (∑ᶠ w : NumberField.FinitePlace K, Bfin w) := by
  classical
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hp
  have hne : Nonempty ι := ⟨i₀⟩
  haveI : Nonempty ι := hne
  -- finite support of the finite-place functions involved
  have hP : Function.HasFiniteSupport
      (fun w : NumberField.FinitePlace K => Real.log (⨆ i, w (p i))) := by
    have hU : (⋃ i : {i : ι // p i ≠ 0},
        Function.mulSupport (fun w : NumberField.FinitePlace K => w (p i.1))).Finite := by
      have h := Set.Finite.biUnion (Set.finite_univ (α := {i : ι // p i ≠ 0}))
        (fun i (_ : i ∈ (Set.univ : Set {i : ι // p i ≠ 0})) =>
          NumberField.FinitePlace.hasFiniteMulSupport (K := K) i.2)
      simpa using h
    refine hU.subset ?_
    intro w hw
    simp only [Function.mem_support] at hw
    simp only [Set.mem_iUnion, Function.mem_mulSupport]
    by_contra h
    simp only [not_exists, not_not] at h
    apply hw
    have hsup : (⨆ i, w (p i)) = 1 := by
      refine le_antisymm ?_ ?_
      · refine ciSup_le (fun i => ?_)
        by_cases hpi : p i = 0
        · rw [hpi]; simp
        · rw [h ⟨i, hpi⟩]
      · have hbdd : BddAbove (Set.range (fun i => w (p i))) :=
          (Set.finite_range (fun i => w (p i))).bddAbove
        have h1 := le_ciSup hbdd i₀
        rw [h ⟨i₀, hi₀⟩] at h1
        exact h1
    rw [hsup, Real.log_one]
  have hF : Function.HasFiniteSupport
      (fun w : NumberField.FinitePlace K => Real.log (w X)) := by
    refine (NumberField.FinitePlace.hasFiniteMulSupport (K := K) hX).subset ?_
    intro w hw
    simp only [Function.mem_support, Function.mem_mulSupport] at hw ⊢
    intro h1
    exact hw (by rw [h1, Real.log_one])
  -- the sum of the multiplicities of the erased places
  have hS : (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ))
      = (Module.finrank ℚ K : ℝ) - ((v₀.mult : ℕ) : ℝ) :=
    LiouvilleAux.sum_mult_erase v₀
  -- step 1: infinite places
  have h1 : (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * Real.log (w X))
      ≤ (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * Real.log (⨆ i, w (p i)))
        + ((∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ))
            * (Real.log (Fintype.card ι : ℝ) + Binf))
        + (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * M w) := by
    have h1a : (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * Real.log (w X))
        ≤ (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * Real.log (⨆ i, w (p i)))
          + (∑ w ∈ Finset.univ.erase v₀,
              ((w.mult : ℕ) : ℝ) * (Real.log (Fintype.card ι : ℝ) + Binf))
          + (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * M w) := by
      calc (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * Real.log (w X))
          ≤ ∑ w ∈ Finset.univ.erase v₀,
              (((w.mult : ℕ) : ℝ) * Real.log (⨆ i, w (p i))
                + ((w.mult : ℕ) : ℝ) * (Real.log (Fintype.card ι : ℝ) + Binf)
                + ((w.mult : ℕ) : ℝ) * M w) := by
            apply Finset.sum_le_sum
            intro w hw
            have h := mul_le_mul_of_nonneg_left (hinf w hw) (Nat.cast_nonneg (w.mult : ℕ))
            calc ((w.mult : ℕ) : ℝ) * Real.log (w X)
                ≤ ((w.mult : ℕ) : ℝ) *
                    (Real.log (⨆ i, w (p i)) + Real.log (Fintype.card ι : ℝ) + Binf + M w) := h
              _ = ((w.mult : ℕ) : ℝ) * Real.log (⨆ i, w (p i))
                    + ((w.mult : ℕ) : ℝ) * (Real.log (Fintype.card ι : ℝ) + Binf)
                    + ((w.mult : ℕ) : ℝ) * M w := by ring
        _ = (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * Real.log (⨆ i, w (p i)))
              + (∑ w ∈ Finset.univ.erase v₀,
                  ((w.mult : ℕ) : ℝ) * (Real.log (Fintype.card ι : ℝ) + Binf))
              + (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * M w) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [← Finset.sum_mul] at h1a
    exact h1a
  -- step 2: finite places
  have h2 : (∑ᶠ w : NumberField.FinitePlace K, Real.log (w X))
      ≤ (∑ᶠ w : NumberField.FinitePlace K, Real.log (⨆ i, w (p i)))
        + (∑ᶠ w : NumberField.FinitePlace K, Bfin w)
        + (∑ᶠ w : NumberField.FinitePlace K, Mf w) := by
    calc (∑ᶠ w : NumberField.FinitePlace K, Real.log (w X))
        ≤ ∑ᶠ w : NumberField.FinitePlace K,
            (Real.log (⨆ i, w (p i)) + Bfin w + Mf w) :=
          finsum_le_finsum hF ((hP.add hBfin_supp).add hMf_supp) (fun w => hfin w)
      _ = (∑ᶠ w : NumberField.FinitePlace K, Real.log (⨆ i, w (p i)))
            + (∑ᶠ w : NumberField.FinitePlace K, Bfin w)
            + (∑ᶠ w : NumberField.FinitePlace K, Mf w) := by
          rw [finsum_add_distrib
                (f := fun w : NumberField.FinitePlace K => Real.log (⨆ i, w (p i)) + Bfin w)
                (g := Mf) (hP.add hBfin_supp) hMf_supp,
              finsum_add_distrib
                (f := fun w : NumberField.FinitePlace K => Real.log (⨆ i, w (p i)))
                (g := Bfin) hP hBfin_supp]
  -- step 3: the height identity isolates the `v₀`-term
  have h3 : (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * Real.log (⨆ i, w (p i)))
      = Height.logHeight p - (∑ᶠ w : NumberField.FinitePlace K, Real.log (⨆ i, w (p i)))
        - ((v₀.mult : ℕ) : ℝ) * Real.log (⨆ i, v₀ (p i)) := by
    have hsum : (∑ w : NumberField.InfinitePlace K, ((w.mult : ℕ) : ℝ) * Real.log (⨆ i, w (p i)))
        = (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * Real.log (⨆ i, w (p i)))
          + ((v₀.mult : ℕ) : ℝ) * Real.log (⨆ i, v₀ (p i)) :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ v₀)).symm
    linarith [hh, hsum]
  rw [hS] at h1
  linarith [h1, h2, h3]

end Work.BW
