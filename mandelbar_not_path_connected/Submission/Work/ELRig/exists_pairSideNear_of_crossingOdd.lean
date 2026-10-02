import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.Inputs
import Submission.Work.ELRig.Sides
import Submission.Work.ELRig.Defs
import Submission.Work.ELRig.side_of_odd_crossings

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# ELRig — odd crossing parity: the real axis lies in the near side

The parity route of `NOTES_LEAD_mandelbar_residuals.md` §3.2 (c): walk down the vertical line
`{Re = x₀}` (`x₀ < -L.R`) from the far end `x₀ + i·ε₁·(R₀+1)` — which is far outside the strip
`|Im| ≤ R₀`, hence lies in the attracting petal `Pa ⊆ pairSide P` — towards the real point `x₀`.
The line meets the two lift curves `γ₁, γ₂` exactly at the crossings of `γ₁` with `Re = x₀`,
whose number is odd by hypothesis, and at every crossing the two sides of the pair curve `P` are
exchanged.  Hence the bottom of the walk, i.e. `Ψ x₀`, lies in the *near* side `pairSideNear P`.

The abstract parity statement is `Work.ELRig.side_of_odd_crossings`; this file feeds it the
concrete data of the lift `L`, the pair `P` and the flower `fl`.
-/

open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

noncomputable section

namespace Work.ELRig

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

theorem exists_pairSideNear_of_crossingOdd {c : ℂ}
    (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (P : Work.EL.CoPair d.hN) (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2)
    (hPy : P.y = d.z₁) (hside : Work.EL.PairSides d.hN P)
    (L : Work.ELRig.RayCylLift d fl) (hPa_far : fl.Pa ⊆ Work.EL.pairSide P)
    {x₀ R₀ ε₁ : ℝ} (hx₀ : x₀ < -L.R) (hRR₀ : R₀ < L.R)
    (hγ : ∀ w : ℂ, w.re < -R₀ → R₀ < |w.im| → fl.Ψ w ∈ fl.Pa)
    (hinj : ∀ s s' : ℝ, L.γ₁ s = L.γ₁ s' → s = s')
    (hfin : ({s : ℝ | (L.γ₁ s).re = x₀}).Finite)
    (hodd : Odd (Set.ncard {s : ℝ | (L.γ₁ s).re = x₀}))
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1)
    (hpos : ∀ s : ℝ, (L.γ₁ s).re = x₀ → 0 < ε₁ * (L.γ₁ s).im)
    (hband1 : ∀ s : ℝ, (L.γ₁ s).re = x₀ → |(L.γ₁ s).im| ≤ R₀)
    (hsep : ∀ t : ℝ, 0 ≤ ε₁ * t → ε₁ * t ≤ R₀ + 1 →
      (((x₀ : ℂ) + t * Complex.I) ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ ↔
        ∃ s : ℝ, (L.γ₁ s).re = x₀ ∧ t = (L.γ₁ s).im))
    (hflip : ∀ s : ℝ, (L.γ₁ s).re = x₀ → ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε →
      ((x₀ : ℂ) + ((L.γ₁ s).im + δ) * Complex.I) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ →
      ((x₀ : ℂ) + ((L.γ₁ s).im - δ) * Complex.I) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ →
      ((fl.Ψ ((x₀ : ℂ) + ((L.γ₁ s).im + δ) * Complex.I) ∈ Work.EL.pairSide P ∧
        fl.Ψ ((x₀ : ℂ) + ((L.γ₁ s).im - δ) * Complex.I) ∈ Work.EL.pairSideNear P) ∨
       (fl.Ψ ((x₀ : ℂ) + ((L.γ₁ s).im + δ) * Complex.I) ∈ Work.EL.pairSideNear P ∧
        fl.Ψ ((x₀ : ℂ) + ((L.γ₁ s).im - δ) * Complex.I) ∈ Work.EL.pairSide P))) :
    fl.Ψ (x₀ : ℂ) ∈ Work.EL.pairSideNear P := by
  -- ## The set of crossings of `γ₁` with the vertical line `Re = x₀`
  have hSfin : ({s : ℝ | (L.γ₁ s).re = x₀}).Finite := hfin
  set Sf : Finset ℝ := hSfin.toFinset with hSf_def
  have hSf_mem : ∀ s : ℝ, s ∈ Sf ↔ (L.γ₁ s).re = x₀ := by
    intro s
    rw [hSf_def]
    exact Set.Finite.mem_toFinset hSfin
  have hSf_card : Sf.card = Set.ncard {s : ℝ | (L.γ₁ s).re = x₀} :=
    (Set.ncard_eq_toFinset_card _ hSfin).symm
  have heps_ne : ε₁ ≠ 0 := by rcases hε₁ with h | h <;> rw [h] <;> norm_num
  have heps_sq : ε₁ * ε₁ = 1 := by rcases hε₁ with h | h <;> rw [h] <;> norm_num
  -- the existence of a crossing forces `R₀ > 0`
  have hR₀ : 0 < R₀ := by
    have hSne : ({s : ℝ | (L.γ₁ s).re = x₀}).Nonempty := by
      refine (Set.ncard_pos hSfin).mp ?_
      obtain ⟨k, hk⟩ := hodd
      rw [hk]
      omega
    obtain ⟨s₀, hs₀⟩ := hSne
    have h1 : |(L.γ₁ s₀).im| ≤ R₀ := hband1 s₀ hs₀
    have h2 : 0 < ε₁ * (L.γ₁ s₀).im := hpos s₀ hs₀
    rcases hε₁ with h | h
    · have him : 0 < (L.γ₁ s₀).im := by rw [h] at h2; simpa using h2
      have h3 : (L.γ₁ s₀).im ≤ R₀ := le_trans (le_abs_self _) h1
      linarith
    · have him : (L.γ₁ s₀).im < 0 := by rw [h] at h2; simpa using h2
      rw [abs_of_neg him] at h1
      linarith
  -- ## The `ε₁·Im`-coordinates of the crossings
  set Uf : Finset ℝ := Sf.image (fun s : ℝ => ε₁ * (L.γ₁ s).im) with hUf_def
  have hinjU : Set.InjOn (fun s : ℝ => ε₁ * (L.γ₁ s).im) (Sf : Set ℝ) := by
    intro s hs s' hs' heq
    refine hinj s s' (Complex.ext ?_ ?_)
    · rw [(hSf_mem s).mp hs, (hSf_mem s').mp hs']
    · exact mul_left_cancel₀ heps_ne heq
  have hUf_card : Uf.card = Sf.card := Finset.card_image_of_injOn hinjU
  have hoddUf : Odd Uf.card := by
    rw [hUf_card, hSf_card]
    exact hodd
  have hUf_spec : ∀ u : ℝ,
      u ∈ Uf ↔ ∃ s : ℝ, (L.γ₁ s).re = x₀ ∧ u = ε₁ * (L.γ₁ s).im := by
    intro u
    rw [hUf_def, Finset.mem_image]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, (hSf_mem s).mp hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, (hSf_mem s).mpr hs, rfl⟩
  have hUf_pos : ∀ u ∈ Uf, 0 < u := by
    intro u hu
    obtain ⟨s, hs, rfl⟩ := (hUf_spec u).mp hu
    exact hpos s hs
  have hUf_le : ∀ u ∈ Uf, u ≤ R₀ := by
    intro u hu
    obtain ⟨s, hs, rfl⟩ := (hUf_spec u).mp hu
    have habs : |ε₁ * (L.γ₁ s).im| = |(L.γ₁ s).im| := by
      rw [abs_mul]
      rcases hε₁ with h | h <;> rw [h] <;> norm_num
    calc ε₁ * (L.γ₁ s).im ≤ |ε₁ * (L.γ₁ s).im| := le_abs_self _
      _ = |(L.γ₁ s).im| := habs
      _ ≤ R₀ := hband1 s hs
  -- ## The vertical line, parametrised so that `ε₁·u` is the imaginary part
  set q : ℝ → ℂ := fun u : ℝ => (x₀ : ℂ) + (((ε₁ * u : ℝ)) : ℂ) * Complex.I with hq_def
  have hq_apply : ∀ u : ℝ, q u = (x₀ : ℂ) + (((ε₁ * u : ℝ)) : ℂ) * Complex.I :=
    fun u => by rw [hq_def]
  have hq_re : ∀ u : ℝ, (q u).re = x₀ := by intro u; rw [hq_apply u]; simp
  have hq_im : ∀ u : ℝ, (q u).im = ε₁ * u := by intro u; rw [hq_apply u]; simp
  have hq_cont : Continuous q := by
    rw [hq_def]
    continuity
  -- ## The line meets the two lift curves exactly at the crossing times
  have hq_curve : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) (R₀ + 1) →
      (q u ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ ↔ u ∈ Uf) := by
    intro u hu
    constructor
    · intro hmem
      have h1 : 0 ≤ ε₁ * (ε₁ * u) := by rw [← mul_assoc, heps_sq, one_mul]; exact hu.1
      have h2 : ε₁ * (ε₁ * u) ≤ R₀ + 1 := by rw [← mul_assoc, heps_sq, one_mul]; exact hu.2
      rw [hq_apply u] at hmem
      obtain ⟨s, hs, hsu⟩ := (hsep (ε₁ * u) h1 h2).mp hmem
      refine (hUf_spec u).mpr ⟨s, hs, ?_⟩
      rw [← hsu, ← mul_assoc, heps_sq, one_mul]
    · rintro huU
      obtain ⟨s, hs, hsu⟩ := (hUf_spec u).mp huU
      have hq_eq : q u = L.γ₁ s := by
        rw [hq_apply u]
        apply Complex.ext
        · simp [hs]
        · rw [hsu, ← mul_assoc, heps_sq, one_mul]
          simp
      exact Or.inl ⟨s, hq_eq.symm⟩
  have hnotcurve : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) (R₀ + 1) → u ∉ Uf →
      q u ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ :=
    fun u hu hnu hmem => hnu ((hq_curve u hu).mp hmem)
  -- ## `Ψ` of a point of the line off the lift curves avoids the pair curve
  have hoff_curve : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) (R₀ + 1) → u ∉ Uf →
      fl.Ψ (q u) ∉ Work.EL.pairCurve P := by
    intro u hu hnu
    have hxR : (q u).re < -L.R := by rw [hq_re u]; exact hx₀
    have hnc := hnotcurve u hu hnu
    intro hmem
    rw [Work.EL.mem_pairCurve_iff] at hmem
    rcases hmem with h | h
    · rw [hPa] at h
      exact hnc (Or.inl (L.tailId₁ (q u) hxR h))
    · rcases h with hy | h
      · rw [hPy] at hy
        exact L.hzne (q u) hxR hy
      · rw [hPb] at h
        exact hnc (Or.inr (L.tailId₂ (q u) hxR h))
  -- ## The far end of the line lies in the petal, hence in the far side
  have htop : fl.Ψ (q (R₀ + 1)) ∈ Work.EL.pairSide P := by
    refine hPa_far (hγ (q (R₀ + 1)) ?_ ?_)
    · rw [hq_re]; linarith
    · rw [hq_im]
      rcases hε₁ with h | h
      · rw [h, one_mul, abs_of_pos (by linarith)]
        linarith
      · rw [h, neg_one_mul, abs_neg, abs_of_pos (by linarith)]
        linarith
  -- ## At a crossing the two sides are exchanged
  have hflip' : ∀ t ∈ Uf, ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε →
      t + δ ∈ Set.Icc (0 : ℝ) (R₀ + 1) → t - δ ∈ Set.Icc (0 : ℝ) (R₀ + 1) →
      t + δ ∉ Uf → t - δ ∉ Uf →
      (fl.Ψ (q (t + δ)) ∈ Work.EL.pairSide P ∧
          fl.Ψ (q (t - δ)) ∈ Work.EL.pairSideNear P) ∨
        (fl.Ψ (q (t + δ)) ∈ Work.EL.pairSideNear P ∧
          fl.Ψ (q (t - δ)) ∈ Work.EL.pairSide P) := by
    intro t ht
    obtain ⟨s, hs, hst⟩ := (hUf_spec t).mp ht
    obtain ⟨e, hepos, he⟩ := hflip s hs
    refine ⟨e, hepos, fun δ hδ hδe h1 h2 h3 h4 => ?_⟩
    have h3' : q (t + δ) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ := hnotcurve (t + δ) h1 h3
    have h4' : q (t - δ) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ := hnotcurve (t - δ) h2 h4
    rcases hε₁ with he1 | he1
    · have him : (L.γ₁ s).im = t := by rw [hst, he1, one_mul]
      have hA : (x₀ : ℂ) + ((L.γ₁ s).im + δ) * Complex.I = q (t + δ) := by
        rw [hq_apply (t + δ)]
        push_cast
        rw [him, he1]
        simp
      have hB : (x₀ : ℂ) + ((L.γ₁ s).im - δ) * Complex.I = q (t - δ) := by
        rw [hq_apply (t - δ)]
        push_cast
        rw [him, he1]
        simp
      have hthis := he δ hδ hδe (by rw [hA]; exact h3') (by rw [hB]; exact h4')
      rw [hA, hB] at hthis
      exact hthis
    · have him : (L.γ₁ s).im = -t := by rw [hst, he1]; ring
      have hA : (x₀ : ℂ) + ((L.γ₁ s).im + δ) * Complex.I = q (t - δ) := by
        rw [hq_apply (t - δ)]
        push_cast
        rw [him, he1]
        push_cast
        ring
      have hB : (x₀ : ℂ) + ((L.γ₁ s).im - δ) * Complex.I = q (t + δ) := by
        rw [hq_apply (t + δ)]
        push_cast
        rw [him, he1]
        push_cast
        ring
      have hthis := he δ hδ hδe (by rw [hA]; exact h4') (by rw [hB]; exact h3')
      rw [hA, hB] at hthis
      tauto
  -- ## The parity lemma
  have hmain : fl.Ψ (q 0) ∈ Work.EL.pairSideNear P :=
    side_of_odd_crossings (A := Work.EL.pairSide P) (B := Work.EL.pairSideNear P)
      (σ := fun u : ℝ => fl.Ψ (q u)) (b := R₀ + 1) (T := Uf)
      hside.isOpen_far hside.isOpen_near hside.disjoint
      (fl.Ψ_diff.continuous.comp hq_cont)
      (fun t ht => hUf_pos t ht)
      (fun t ht => by have := hUf_le t ht; linarith)
      hoddUf
      (fun t ht hnt => hside.mem_or_mem (hoff_curve t ht hnt))
      hflip' htop
  simpa [hq_apply 0] using hmain

end Work.ELRig
