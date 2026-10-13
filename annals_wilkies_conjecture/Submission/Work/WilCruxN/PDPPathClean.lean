/-
  Work.WilCrux.PDPPath — the path-gain step of node N4c.

  Given a def±inable choice function `ζ` with values in a gain locus `Es` and the mean-value
  bounds along a segment `[w₁, w₁ + L e_i]`, this module assembles the
  `PathGainBound` estimate `η·L ≤ C·τ` for every small `τ`, with `C` controlled by the
  uniform break-point count of `MonotonePiecesOnLine`.
-/
import Mathlib
import Submission.Work.WilCruxN.PDPDefsClean
import Submission.Work.WilCrux.PathGainBound

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilCruxN

open Work.WilCrux

open WilkiesDesign WilkiesDesign.CG

/-! ## The path-gain step -/

/-- Along the segment `s ↦ w₁ + s • e_i`, if `ζ (w₁ + s • e_i) τ` is a gain witness for every
`s ∈ [0,L]` and `τ > 0`, then `η * L` is `O(τ)`. -/
theorem pdp_path_step {a b : ℕ} (S : WilkiesDesign.SOMin) (hcd : S.SharpCD)
    (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (i : Fin a)
    (Fs : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (ζ : (Fin a → ℝ) → ℝ → (Fin b → ℝ))
    (Es : Set (Fin (a + b) → ℝ)) (Q₂ : Set (Fin a → ℝ))
    (Fz : ℕ) (bz : Polynomial ℕ) (D : ℕ)
    (hζgraph : ∀ j : Fin b, WilkiesDesign.graphOf (fun x : Fin (a + 1) → ℝ =>
        ζ (fun i' : Fin a => x (Fin.castSucc i')) (x (Fin.last a)) j)
        ∈ S.Ω Fz (bz.eval D) (a + 1 + 1))
    (w₁ : Fin a → ℝ) (L τ₀ M ηk r0 : ℝ)
    (hηkpos : 0 < ηk) (hLpos : 0 < L) (hτ₀pos : 0 < τ₀) (hr0 : 0 < r0) (hM : 0 ≤ M)
    (hτ₀r0 : τ₀ ≤ r0)
    (hseg : ∀ s ∈ Set.Icc (0 : ℝ) L, w₁ + s • Pi.single i 1 ∈ Q₂)
    (hQ₂sub : Q₂ ⊆ pdpAcc Es)
    (hEs_gain : ∀ u ∈ Es, ηk ≤ Work.WilG4b.dDir (Work.WilG4c.famFun Fs) (Fin.castAdd b i) u)
    (hEs_c1 : ∀ u ∈ Es, ContDiffAt ℝ 1 (Work.WilG4c.famFun Fs) u)
    (hζ : ∀ (w : Fin a → ℝ) (τ : ℝ), (∃ z : Fin b → ℝ, 0 < ‖z‖ ∧ ‖z‖ ≤ τ ∧
        Fin.append w z ∈ Es) →
        0 < ‖ζ w τ‖ ∧ ‖ζ w τ‖ ≤ τ ∧ Fin.append w (ζ w τ) ∈ Es)
    (hdiffball : ∀ s ∈ Set.Icc (0 : ℝ) L, ∀ z ∈ Metric.closedBall (0 : Fin b → ℝ) τ₀,
        DifferentiableAt ℝ (G (w₁ + s • Pi.single i 1)) z)
    (hderb : ∀ s ∈ Set.Icc (0 : ℝ) L, ∀ z : Fin b → ℝ, ‖z‖ ≤ τ₀ →
        ‖fderiv ℝ (G (w₁ + s • Pi.single i 1)) z‖ ≤ M)
    (hFs_lip : ∀ (w : Fin a → ℝ) (z z' : Fin b → ℝ), |Fs w z - Fs w z'| = |G w z - G w z'|)
    (hFs_small : ∀ (w : Fin a → ℝ) (z : Fin b → ℝ), |Fs w z| = |G w z - G w 0|) :
    ∃ K : ℕ, ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀,
      ηk * L ≤ ((↑K : ℝ) + 2) * (2 * ((b : ℝ) + 1) * M + 1) * τ := by
  obtain ⟨K, hK⟩ := pdp_monoPieces_stub (n := a + 1) S hcd Fz (Polynomial.eval D bz)
    (Fin.castSucc i)
  refine ⟨b * K, ?_⟩
  intro τ hτ
  have hτpos : 0 < τ := hτ.1
  have hτr0 : τ < r0 := lt_of_lt_of_le hτ.2 hτ₀r0
  let ψ : ℝ → (Fin b → ℝ) := fun s => ζ (w₁ + s • Pi.single i 1) τ
  have hwit : ∀ s ∈ Set.Icc (0 : ℝ) L, ∃ z : Fin b → ℝ,
      0 < ‖z‖ ∧ ‖z‖ ≤ τ ∧ Fin.append (w₁ + s • Pi.single i 1) z ∈ Es := by
    intro s hs
    obtain ⟨z, hz1, hz2, hz3⟩ := hQ₂sub (hseg s hs) (min τ r0) (lt_min hτpos hr0)
    exact ⟨z, hz1, le_of_lt (lt_of_lt_of_le hz2 (min_le_left _ _)), hz3⟩
  have hmemψ : ∀ s ∈ Set.Icc (0 : ℝ) L,
      Fin.append (w₁ + s • Pi.single i 1) (ψ s) ∈ Es := by
    intro s hs
    exact (hζ _ _ (hwit s hs)).2.2
  have hnormψ : ∀ s ∈ Set.Icc (0 : ℝ) L, ‖ψ s‖ ≤ τ := by
    intro s hs
    exact (hζ _ _ (hwit s hs)).2.1
  -- the break set of the coordinate functions
  have hbrkex : ∀ j : Fin b, ∃ brk : Finset ℝ, brk.card ≤ K ∧
      (∀ s : ℝ, s ∉ brk → DifferentiableAt ℝ (fun t : ℝ => ζ (w₁ + t • Pi.single i 1) τ j) s) ∧
      (∀ s t : ℝ, s < t → (∀ u ∈ Set.Ioo s t, u ∉ brk) →
        MonotoneOn (fun t : ℝ => ζ (w₁ + t • Pi.single i 1) τ j) (Set.Ioo s t) ∨
        AntitoneOn (fun t : ℝ => ζ (w₁ + t • Pi.single i 1) τ j) (Set.Ioo s t)) := by
    intro j
    have hnode : (fun t : ℝ => ζ (fun i' => ((Fin.snoc w₁ τ + t • Pi.single (Fin.castSucc i) (1 : ℝ)) : Fin (a+1) → ℝ) i'.castSucc) (((Fin.snoc w₁ τ + t • Pi.single (Fin.castSucc i) (1 : ℝ)) : Fin (a+1) → ℝ) (Fin.last a)) j) = fun t : ℝ => ζ (w₁ + t • Pi.single i 1) τ j := by
      funext t
      congr 2
      · funext i'
        rw [Pi.add_apply, Pi.smul_apply, Pi.single_apply, Fin.snoc_castSucc]
        by_cases h : i' = i
        · subst h; simp
        · have hne : ¬(Fin.castSucc i' = Fin.castSucc i) := fun hh =>
            h (Fin.castSucc_inj.mp hh)
          simp [h, hne]
      · rw [Pi.add_apply, Pi.smul_apply, Pi.single_apply, Fin.snoc_last]
        have hne : Fin.last a ≠ Fin.castSucc i := by
          intro hh
          have := congrArg Fin.val hh
          simp [Fin.val_last, Fin.val_castSucc] at this
          omega
        simp [hne]
    obtain ⟨brk, hcard, hdiffj, hmonoj⟩ := hK _ (hζgraph j) (Fin.snoc w₁ τ)
    exact ⟨brk, hcard, fun s hs => by rw [← hnode]; exact hdiffj s hs,
      fun s t hst hav => by
        rw [← hnode]
        exact hmonoj s t hst (fun u hu hmem => hav u hu hmem)⟩
  choose brk_j hbrk_card hbrk_diff hbrk_mono using hbrkex
  set brk : Finset ℝ := Finset.univ.biUnion brk_j with hbrkdef
  have hmem_brk : ∀ (j : Fin b) (s : ℝ), s ∈ brk_j j → s ∈ brk := by
    intro j s hs
    rw [hbrkdef]
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hs⟩
  have hbrkcard : brk.card ≤ b * K := by
    rw [hbrkdef]
    calc (Finset.univ.biUnion brk_j).card ≤ ∑ j ∈ Finset.univ, (brk_j j).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ Finset.univ, K := Finset.sum_le_sum (fun j _ => hbrk_card j)
      _ = b * K := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hbrkdiff : ∀ s ∈ Set.Ioo (0 : ℝ) L, s ∉ brk → DifferentiableAt ℝ ψ s := by
    intro s hs hbrks
    rw [show ψ = fun s => ζ (w₁ + s • Pi.single i 1) τ from rfl]
    rw [differentiableAt_pi]
    intro j
    exact hbrk_diff j s (fun hmem => hbrks (hmem_brk j s hmem))
  have hbrkmono : ∀ k : Fin b, ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ L →
      (∀ u ∈ Set.Ioo s t, u ∉ brk) →
      MonotoneOn (fun u => ψ u k) (Set.Ioo s t) ∨ AntitoneOn (fun u => ψ u k) (Set.Ioo s t) := by
    intro k s t _ hst _ hav
    rw [show ψ = fun s => ζ (w₁ + s • Pi.single i 1) τ from rfl]
    exact hbrk_mono k s t hst (fun u hu hmem => hav u hu (hmem_brk k u hmem))
  -- the two remaining hypotheses of `PathGainBound`
  have hLip : ∀ s ∈ Set.Icc (0 : ℝ) L, ∀ z z' : Fin b → ℝ, ‖z‖ ≤ τ → ‖z'‖ ≤ τ →
      |Fs (w₁ + s • Pi.single i 1) z - Fs (w₁ + s • Pi.single i 1) z'| ≤ M * ‖z - z'‖ := by
    intro s hs z z' hz hz'
    have hzτ₀ : ‖z‖ ≤ τ₀ := le_trans hz (le_of_lt hτ.2)
    have hz'τ₀ : ‖z'‖ ≤ τ₀ := le_trans hz' (le_of_lt hτ.2)
    have hbnd : ∀ u ∈ Metric.closedBall (0 : Fin b → ℝ) τ₀,
        ‖fderiv ℝ (G (w₁ + s • Pi.single i 1)) u‖ ≤ M := by
      intro u hu
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hu
      exact hderb s hs u hu
    have hdiff : ∀ u ∈ Metric.closedBall (0 : Fin b → ℝ) τ₀,
        DifferentiableAt ℝ (G (w₁ + s • Pi.single i 1)) u := by
      intro u hu
      exact hdiffball s hs u hu
    have h := (pdp_lip_of_bound (G := G) (w := w₁ + s • Pi.single i 1)
      (τ := τ₀) (M := M) hτ₀pos.le hM hdiff hbnd).1 z z' hzτ₀ hz'τ₀
    rwa [hFs_lip]
  have hsmall : ∀ s ∈ Set.Icc (0 : ℝ) L, ∀ z : Fin b → ℝ, ‖z‖ ≤ τ →
      |Fs (w₁ + s • Pi.single i 1) z| ≤ M * ‖z‖ := by
    intro s hs z hz
    have hzτ₀ : ‖z‖ ≤ τ₀ := le_trans hz (le_of_lt hτ.2)
    have hbnd : ∀ u ∈ Metric.closedBall (0 : Fin b → ℝ) τ₀,
        ‖fderiv ℝ (G (w₁ + s • Pi.single i 1)) u‖ ≤ M := by
      intro u hu
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hu
      exact hderb s hs u hu
    have hdiff : ∀ u ∈ Metric.closedBall (0 : Fin b → ℝ) τ₀,
        DifferentiableAt ℝ (G (w₁ + s • Pi.single i 1)) u := by
      intro u hu
      exact hdiffball s hs u hu
    have h := (pdp_lip_of_bound (G := G) (w := w₁ + s • Pi.single i 1)
      (τ := τ₀) (M := M) hτ₀pos.le hM hdiff hbnd).2 z hzτ₀
    rwa [hFs_small]
  have hC1ψ : ∀ s ∈ Set.Icc (0 : ℝ) L,
      ContDiffAt ℝ 1 (Work.WilG4c.famFun Fs) (Fin.append (w₁ + s • Pi.single i 1) (ψ s)) := by
    intro s hs
    exact hEs_c1 _ (hmemψ s hs)
  have hgainψ : ∀ s ∈ Set.Icc (0 : ℝ) L,
      ηk ≤ fderiv ℝ (Work.WilG4c.famFun Fs)
        (Fin.append (w₁ + s • Pi.single i 1) (ψ s)) (Fin.append (Pi.single i 1) 0) := by
    intro s hs
    have h := hEs_gain _ (hmemψ s hs)
    rwa [Work.WilG4b.dDir, pdp_single_castAdd i] at h
  exact Work.WilCrux.PathGainBound Fs i w₁ L τ M (ηk) hLpos hτpos hM
    ψ (b * K) brk hbrkcard hnormψ hbrkdiff hbrkmono hLip hsmall hC1ψ hgainψ

end Work.WilCruxN
