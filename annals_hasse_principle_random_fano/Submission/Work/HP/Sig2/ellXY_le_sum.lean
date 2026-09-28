import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.lam_basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Filter

namespace Work.HP.Sig2

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


end Work.HP.Sig2
