import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.lam_basic
import Submission.Work.HP.schmidt_sum_form
import Submission.Work.HP.num_lattices
import Submission.Work.HP.minkowski_upper
import Submission.Work.HP.dmin_le_exists_prim
import Submission.Work.HP.dyadic_sum_ge3
import Submission.Work.HP.kwin_spec
import Submission.Work.HP.ball_count_small
import Submission.Work.HP.window_sum_arith
import Submission.Work.HP.dyadic_sum_r2
import Submission.Work.HP.window_arith_r2
import Submission.Work.HP.prim_lat_window_finite
import Submission.Work.HP.ball_prod_window_ge3
import Submission.Work.HP.ball_prod_window_r2
import Submission.Work.HP.window_sum_ge3
import Submission.Work.HP.window_sum_r2

/-!
# N05: pair counts `\ell_{r,n}(X,Y;\Delta) \ll X^r Y^r \Delta^{n-1} (\log \Delta)^{2\min(r-2,1)}`

This file contains the reduction of the pair count to a sum over primitive lattices
(`ellXY_le_sum`) and the top-level assembly `pair_counts_core`, together with the
elementary helpers.  The analytic inputs are the lemmas proved in the sibling files
listed in the imports below.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Filter

namespace Work.HP

open scoped BigOperators



variable {ι : Type*} [Fintype ι]

lemma abs_apply_le_eNorm (v : ι → ℤ) (i : ι) : |((v i : ℤ) : ℝ)| ≤ eNorm v := by
  have h1 : ((v i : ℝ)) ^ 2 ≤ ∑ j, ((v j : ℝ)) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ((v j : ℝ))) (Finset.mem_univ i)
  have h2 := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq_eq_abs] at h2
  exact h2

lemma finite_eNorm_le (X : ℝ) : {v : ι → ℤ | eNorm v ≤ X}.Finite := by
  classical
  refine Set.Finite.subset
    (Finset.finite_toSet (Fintype.piFinset (fun _ : ι => Finset.Icc (-(⌈X⌉₊ : ℤ)) (⌈X⌉₊ : ℤ)))) ?_
  intro v hv
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro i
  have h3 : |((v i : ℤ) : ℝ)| ≤ X := le_trans (abs_apply_le_eNorm v i) hv
  have h4 : ((v i : ℤ) : ℝ) ≤ (⌈X⌉₊ : ℝ) := by
    have := abs_le.mp h3; linarith [this.2, Nat.le_ceil X]
  have h5 : -(⌈X⌉₊ : ℝ) ≤ ((v i : ℤ) : ℝ) := by
    have := abs_le.mp h3; linarith [this.1, Nat.le_ceil X]
  simp only [Finset.mem_Icc]
  constructor <;> [exact_mod_cast h5; exact_mod_cast h4]

lemma li_swap {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {a b : M}
    (h : LinearIndependent R ![a, b]) : LinearIndependent R ![b, a] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  have h' := h t s (by simpa [add_comm] using hst)
  exact ⟨h'.2, h'.1⟩

lemma ellXY_comm (n r : ℕ) (X Y Δ : ℝ) : ellXY n r X Y Δ = ellXY n r Y X Δ := by
  simp only [ellXY]
  apply Set.ncard_congr (fun p _ => (p.2, p.1))
  · intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hp
    refine ⟨li_swap h1, h3, h2, ?_⟩
    show dmin r {p.2, p.1} ≤ Δ
    simpa only [Set.pair_comm p.1 p.2] using h4
  · intro p q hp hq h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 h.1
  · intro q hq
    refine ⟨(q.2, q.1), ?_, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := hq
    refine ⟨li_swap h1, h3, h2, ?_⟩
    show dmin r {q.2, q.1} ≤ Δ
    simpa only [Set.pair_comm q.1 q.2] using h4

lemma ellXY_le_sum (n r : ℕ) (hr : 2 ≤ r) (hrn : r ≤ n + 1)
    (hred : ∀ (x y : Fin (n+1) → ℤ) (D : ℝ), LinearIndependent ℤ ![x, y] → dmin r {x, y} ≤ D →
      ∃ L : Submodule ℤ (Fin (n+1) → ℤ), IsPrimLat L ∧ rk L = r ∧ x ∈ L ∧ y ∈ L ∧ detL L ≤ D + 1)
    (X Y Δ : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hΔ : 1 ≤ Δ) (hXY : X ≤ Y) :
    ∃ T : Finset (Submodule ℤ (Fin (n+1) → ℤ)),
      (∀ L ∈ T, IsPrimLat L ∧ rk L = r ∧ detL L ≤ Δ + 1 ∧ lam L 1 ≤ X ∧ lam L 2 ≤ Y) ∧
      ((ellXY n r X Y Δ : ℝ) ≤ ∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ)) := by
  classical
  have hLIne : ∀ p : (Fin (n+1) → ℤ) × (Fin (n+1) → ℤ),
      LinearIndependent ℤ ![p.1, p.2] → p.1 ≠ 0 := by
    intro p hp h
    rw [h] at hp
    rw [LinearIndependent.pair_iff] at hp
    have := (hp 1 0 (by simp)).1
    exact one_ne_zero this
  set S : Set ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)) :=
    {p | LinearIndependent ℤ ![p.1, p.2] ∧ eNorm p.1 ≤ X ∧ eNorm p.2 ≤ Y ∧ dmin r {p.1, p.2} ≤ Δ} with hSdef
  have hSfin : S.Finite := by
    rw [hSdef]
    refine Set.Finite.subset ((finite_eNorm_le X).prod (finite_eNorm_le Y)) ?_
    intro p hp
    exact ⟨hp.2.1, hp.2.2.1⟩
  let g : ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)) → Submodule ℤ (Fin (n+1) → ℤ) := fun p =>
    if hp : p ∈ S then Classical.choose (hred p.1 p.2 Δ hp.1 hp.2.2.2) else ⊥
  have hg : ∀ p ∈ S, IsPrimLat (g p) ∧ rk (g p) = r ∧ p.1 ∈ g p ∧ p.2 ∈ g p ∧ detL (g p) ≤ Δ + 1 := by
    intro p hp
    rw [show g p = Classical.choose (hred p.1 p.2 Δ hp.1 hp.2.2.2) from dif_pos hp]
    exact Classical.choose_spec (hred p.1 p.2 Δ hp.1 hp.2.2.2)
  refine ⟨(hSfin.toFinset).image g, ?_, ?_⟩
  · intro L hL
    rw [Finset.mem_image] at hL
    obtain ⟨p, hp, rfl⟩ := hL
    have hpS : p ∈ S := by rwa [Set.Finite.mem_toFinset] at hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hg p hpS
    refine ⟨h1, h2, h5, ?_, ?_⟩
    · exact le_trans ((lam_basic (Fin (n+1)) (g p)).2.2.2.1 p.1 h3 (hLIne p hpS.1)) hpS.2.1
    · refine le_trans ((lam_basic (Fin (n+1)) (g p)).2.2.2.2 p.1 p.2 h3 h4 hpS.1) ?_
      exact max_le (le_trans hpS.2.1 hXY) hpS.2.2.1
  · have hcard : (S.ncard : ℝ) = ∑ L ∈ (hSfin.toFinset).image g,
        (((hSfin.toFinset).filter (fun p => g p = L)).card : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ hSfin]
      rw [Finset.card_eq_sum_card_fiberwise (f := g) (s := hSfin.toFinset)
        (t := (hSfin.toFinset).image g) (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)]
      push_cast
      rfl
    rw [ellXY, ← hSdef]
    rw [hcard]
    refine Finset.sum_le_sum (fun L hL => ?_)
    obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.mp hL
    have hp₀S : p₀ ∈ S := by rwa [Set.Finite.mem_toFinset] at hp₀
    obtain ⟨-, -, h3, h4, -⟩ := hg p₀ hp₀S
    have hPLfin : ({v : Fin (n+1) → ℤ | v ∈ g p₀ ∧ eNorm v ≤ X}).Finite :=
      (finite_eNorm_le X).subset (fun v hv => hv.2)
    have hPMfin : ({v : Fin (n+1) → ℤ | v ∈ g p₀ ∧ eNorm v ≤ Y}).Finite :=
      (finite_eNorm_le Y).subset (fun v hv => hv.2)
    have hsub : ((hSfin.toFinset).filter (fun p => g p = g p₀)) ⊆
        (hPLfin.toFinset ×ˢ hPMfin.toFinset) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpT, hpg⟩ := hp
      have hpS : p ∈ S := by rwa [Set.Finite.mem_toFinset] at hpT
      obtain ⟨-, -, h1, h2, -⟩ := hg p hpS
      rw [Finset.mem_product]
      refine ⟨?_, ?_⟩
      · rw [Set.Finite.mem_toFinset]
        exact ⟨by rw [← hpg]; exact h1, hpS.2.1⟩
      · rw [Set.Finite.mem_toFinset]
        exact ⟨by rw [← hpg]; exact h2, hpS.2.2.1⟩
    have hfib : (((hSfin.toFinset).filter (fun p => g p = g p₀)).card : ℝ) ≤
        ((hPLfin.toFinset ×ˢ hPMfin.toFinset).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    refine le_trans hfib ?_
    rw [Finset.card_product]
    push_cast
    have h1 : hPLfin.toFinset.card = ballCount (g p₀) X := by
      rw [← Set.ncard_eq_toFinset_card _ hPLfin]; rfl
    have h2 : hPMfin.toFinset.card = ballCount (g p₀) Y := by
      rw [← Set.ncard_eq_toFinset_card _ hPMfin]; rfl
    rw [h1, h2]

lemma pair_counts_core (n r : ℕ) (hn : 2 ≤ n) (hr : 2 ≤ r) (hrn : r ≤ n + 1)
    (hred : ∀ (x y : Fin (n+1) → ℤ) (D : ℝ), LinearIndependent ℤ ![x, y] → dmin r {x, y} ≤ D →
      ∃ L : Submodule ℤ (Fin (n+1) → ℤ), IsPrimLat L ∧ rk L = r ∧ x ∈ L ∧ y ∈ L ∧ detL L ≤ D + 1)
    (Kws : ℝ) (hKwspos : 0 < Kws)
    (hws : ∀ (X Y Δ : ℝ) (T : Finset (Submodule ℤ (Fin (n+1) → ℤ))),
      1 ≤ X → 1 ≤ Y → 1 ≤ Δ → X ≤ Y →
      (∀ L ∈ T, IsPrimLat L ∧ rk L = r ∧ detL L ≤ Δ + 1 ∧ lam L 1 ≤ X ∧ lam L 2 ≤ Y) →
      (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ)) ≤
        Kws * X ^ r * Y ^ r * Δ ^ (n - 1) * Real.log (2 * Δ) ^ (2 * min (r - 2) 1)) :
    ∃ K : ℝ, 0 < K ∧ ∀ X Y Δ : ℝ, 1 ≤ X → 1 ≤ Y → 1 ≤ Δ →
      (ellXY n r X Y Δ : ℝ) ≤ K * X ^ r * Y ^ r * Δ ^ (n - 1) *
        Real.log (2 * Δ) ^ (2 * min (r - 2) 1) := by
  refine ⟨Kws, hKwspos, ?_⟩
  intro X Y Δ hX hY hΔ
  rcases le_total X Y with hXY | hYX
  · obtain ⟨T, hT, hle⟩ := ellXY_le_sum n r hr hrn hred X Y Δ hX hY hΔ hXY
    exact le_trans hle (hws X Y Δ T hX hY hΔ hXY hT)
  · rw [ellXY_comm n r X Y Δ]
    obtain ⟨T, hT, hle⟩ := ellXY_le_sum n r hr hrn hred Y X Δ hY hX hΔ hYX
    refine le_trans hle (le_trans (hws Y X Δ T hY hX hΔ hYX hT) ?_)
    apply le_of_eq
    ring


/-- N05. Pair counts `ℓ_{r,n}(X,Y;Δ) ≪ X^r Y^r Δ^{n-1} (log Δ)^{2 min(r-2,1)}`. -/
theorem pair_counts (n : ℕ) (hn : 2 ≤ n) (r : ℕ) (hr : 2 ≤ r) (hrn : r ≤ n + 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ X Y Δ : ℝ, 1 ≤ X → 1 ≤ Y → 1 ≤ Δ →
      (ellXY n r X Y Δ : ℝ)
        ≤ K * X ^ r * Y ^ r * Δ ^ (n - 1) * Real.log (2 * Δ) ^ (2 * min (r - 2) 1) := by
  classical
  -- ## inputs from the sibling lemmas
  obtain ⟨K1, hK1pos, hK1⟩ := schmidt_sum_form (Fin (n + 1))
  obtain ⟨K2, hK2pos, hK2⟩ := num_lattices (Fin (n + 1))
  obtain ⟨K3, hK3pos, hmink0⟩ := minkowski_upper (Fin (n + 1))
  obtain ⟨K8, hK8pos, hK8_1, hK8_2, hK8_3⟩ := ball_count_small (Fin (n + 1)) ⟨K1, hK1pos, hK1⟩
  -- ## the reduction hypothesis
  have hred : ∀ (x y : Fin (n + 1) → ℤ) (D : ℝ), LinearIndependent ℤ ![x, y] → dmin r {x, y} ≤ D →
      ∃ L : Submodule ℤ (Fin (n + 1) → ℤ), IsPrimLat L ∧ rk L = r ∧ x ∈ L ∧ y ∈ L ∧ detL L ≤ D + 1 :=
    fun x y D hxy hd => dmin_le_exists_prim (Fin (n + 1)) r x y D hxy hr (by simpa using hrn) hd
  -- ## Minkowski with a constant `≥ 1`
  set Kmink : ℝ := max K3 1 with hKminkdef
  have hKmink1 : 1 ≤ Kmink := le_max_right _ _
  have hmink : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)),
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ Kmink * detL L := by
    intro L
    have h0 : (0 : ℝ) ≤ detL L := Real.sqrt_nonneg _
    calc (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ K3 * detL L := hmink0 L
      _ ≤ Kmink * detL L := by
          rw [hKminkdef]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) h0
  -- ## the Finset form of the lattice count
  have hnumF : ∀ (s : Fin r → ℝ) (F : Finset (Submodule ℤ (Fin (n + 1) → ℤ))), (∀ j, 1 ≤ s j) →
      (∀ L ∈ F, IsPrimLat L ∧ rk L = r ∧ ∀ j : Fin r, lam L (j.1 + 1) ≤ s j) →
      ((F.card : ℝ) ≤ K2 * ∏ j : Fin r, s j ^ (n + 1 + r + 1 - 2 * (j.1 + 1))) := by
    intro s F hs hF
    have hf := prim_lat_window_finite (Fin (n + 1)) r s hs
    have h1 : (F.card : ℝ) ≤
        (({L : Submodule ℤ (Fin (n + 1) → ℤ) | IsPrimLat L ∧ rk L = r ∧
            ∀ j : Fin r, lam L (j.1 + 1) ≤ s j}.ncard : ℝ)) := by
      have hsub : F ⊆ hf.toFinset := fun L hL => by
        rw [Set.Finite.mem_toFinset]; exact hF L hL
      have h2 : F.card ≤ hf.toFinset.card := Finset.card_le_card hsub
      have h3 : hf.toFinset.card =
          ({L : Submodule ℤ (Fin (n + 1) → ℤ) | IsPrimLat L ∧ rk L = r ∧
            ∀ j : Fin r, lam L (j.1 + 1) ≤ s j} : Set (Submodule ℤ (Fin (n + 1) → ℤ))).ncard :=
        (Set.ncard_eq_toFinset_card _ hf).symm
      rw [h3] at h2
      exact_mod_cast h2
    exact le_trans h1 (by simpa [Fintype.card_fin] using hK2 r s hs)
  -- ## kwin_spec
  have hwin : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)), rk L = r →
      (∀ j : Fin r, lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin r L j)) ∧
      (∀ j : Fin r, (2 : ℝ) ^ (kwin r L j) ≤ 2 * lam L (j.1 + 1)) ∧
      Monotone (kwin r L) ∧
      (∀ M : ℝ, 1 ≤ M → (∏ j : Fin r, (2 : ℝ) ^ (kwin r L j)) ≤ M →
        (∑ j : Fin r, kwin r L j) ≤ ⌈Real.logb 2 M⌉₊) :=
    fun L hL => kwin_spec (Fin (n + 1)) r L hr hL
  rcases eq_or_ne r 2 with hr2 | hr2
  · -- ## the case `r = 2`
    subst hr2
    have hbp := ball_prod_window_r2 n hn K8 hK8pos hK8_3 hK8_2
    obtain ⟨Cdy, hCdyp, hdy0⟩ := dyadic_sum_r2 (n + 1) (by omega)
    have hdy : ∀ (X Y L' : ℝ), 1 ≤ X → 1 ≤ Y → 0 ≤ L' →
        (∑ k ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range (⌈L'⌉₊ + 1)),
          (if Monotone k ∧ (∑ j, k j) ≤ ⌈L'⌉₊ ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y then
            X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1)
              + X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1)
              + Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1)
          else 0)) ≤ Cdy * X ^ 2 * Y ^ 2 * 2 ^ (((n : ℝ) + 1 - 2) * L') := by
      intro X Y L' h1 h2 h3
      have h := hdy0 X Y L' h1 h2 h3
      have hcast : ((↑(n + 1) : ℝ) - 2) * L' = ((↑n : ℝ) + 1 - 2) * L' := by push_cast; ring
      rwa [hcast] at h
    obtain ⟨Karith, hKarithpos, harith⟩ := window_arith_r2 n hn Kmink hKmink1 Cdy hCdyp hdy
    refine pair_counts_core n 2 hn hr hrn hred (K2 * K8 ^ 2 * 16 * Karith) (by positivity) ?_
    intro X Y Δ T hX hY hΔ hXY hT
    have hmain := window_sum_r2 n hn K2 hK2pos hnumF Kmink hKmink1 hmink hwin K8 hK8pos
      hK8_3 hK8_2 (fun L k X' Y' hrL hk2 h1 h2 h12 h3 h4 => hbp L hrL k hk2 X' Y' h1 h2 h12 h3 h4)
      Karith hKarithpos harith X Y Δ hX hY hΔ hXY T hT
    simpa using hmain
  · -- ## the case `r ≥ 3`
    have hr3 : 3 ≤ r := by omega
    have hbp := ball_prod_window_ge3 n r hn hr3 hrn K8 hK8pos hK8_1 hK8_2
    obtain ⟨Cdy, hCdyp, hdy0⟩ := dyadic_sum_ge3 (n + 1) r hr3 (by omega)
    have hdy : ∀ (L' : ℝ), 0 ≤ L' →
        (∑ k ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (⌈L'⌉₊ + 1)),
          (if Monotone k ∧ (∑ j, k j) ≤ ⌈L'⌉₊ then
            (2 : ℝ) ^ (∑ j : Fin r, k j * (if (j.1 : ℕ) < 2 then (n + 1) - 2 else (n + 1) + r - 1 - 2 * j.1))
          else 0)) ≤ Cdy * 2 ^ (((n : ℝ) + 1 - 2) * L') * (1 + L') ^ 2 := by
      intro L' h
      have h0 := hdy0 L' h
      have hcast : ((↑(n + 1) : ℝ) - 2) * L' = ((↑n : ℝ) + 1 - 2) * L' := by push_cast; ring
      rwa [hcast] at h0
    obtain ⟨Karith, hKarithpos, harith⟩ := window_sum_arith n r hn hr3 hrn Kmink hKmink1 Cdy hCdyp hdy
    refine pair_counts_core n r hn hr hrn hred
      (K2 * K8 ^ 2 * (2 : ℝ) ^ (2 * r) * Karith) (by positivity) ?_
    intro X Y Δ T hX hY hΔ hXY hT
    refine window_sum_ge3 n r hn hr3 hrn K2 hK2pos hnumF Kmink hKmink1 hmink hwin K8 hK8pos
      hK8_1 hK8_2 ?_ Karith hKarithpos harith X Y Δ hX hY hΔ hXY T hT
    intro L k X' Y' hrL hk2 h1 h2 h3 h4
    exact hbp L hrL k hk2 X' Y' h1 h2 h3 h4

end Work.HP
