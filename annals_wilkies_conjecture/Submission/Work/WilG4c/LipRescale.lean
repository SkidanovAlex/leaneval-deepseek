import Mathlib
import Submission.Work.WilG4c.LipDefs
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG4c.FamGraphRescale
import Submission.Work.WilG4c.ChartRescaleMem
import Submission.Work.WilG4c.RescalePredicates
import Submission.Work.WilG4c.GridIndex
import Submission.Work.WilG4c.ShiftB
import Submission.Work.WilG4c.ShiftC
import Submission.Work.WilG4c.TileCover

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

-- The vocabulary of this area (`FLemP`, `PY`, `ChartsOK`, ...) is declared in the
-- namespace `Work.WilkG4c` (the module spelling); the delegated lemmas of this
-- development live next to this file in `Work.WilG4c` (the directory spelling).
open Work.WilkG4c

/-- The corner `j/K` of the tile indexed by `j` (the mesh of the grid is `1/K`). -/
def tileQ {n : ℕ} (M : ℕ) (j : Fin (n + 1) → Fin (M + 1)) : Fin (n + 1) → ℝ :=
  fun b => ((j b : ℕ) : ℝ) / (((M + 1 : ℕ)) : ℝ)

/-- The rescaled family on the tile indexed by `j`: `z ↦ F(·, j/K + z/K)`. -/
def tileFam {k p n : ℕ} (M : ℕ) (j : Fin (n + 1) → Fin (M + 1))
    (F : Family k p (n + 1)) : Family k p (n + 1) :=
  fun i l z => F i l (fun b => tileQ M j b + z b / (((M + 1 : ℕ)) : ℝ))

/-- The affine injection `ψ ↦ q + ψ/K` on chart tuples. -/
def chartEmb {p n : ℕ} (K : ℕ) (hK : 0 < K) (q : Fin n → ℝ) :
    ChartTuple p n ↪ ChartTuple p n where
  toFun ψ := fun j l t => q j + ψ j l t / (K : ℝ)
  inj' := by
    intro ψ ψ' h
    funext j l t
    have h' : q j + ψ j l t / (K : ℝ) = q j + ψ' j l t / (K : ℝ) :=
      congrFun (congrFun (congrFun h j) l) t
    have hK' : (K : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
      exact ne_of_gt this
    have e1 : ψ j l t / (K : ℝ) = ψ' j l t / (K : ℝ) := add_left_cancel h'
    calc ψ j l t = ψ j l t / (K : ℝ) * (K : ℝ) := (div_mul_cancel₀ _ hK').symm
      _ = ψ' j l t / (K : ℝ) * (K : ℝ) := by rw [e1]
      _ = ψ' j l t := div_mul_cancel₀ _ hK'

theorem LipRescale (S : WilkiesDesign.SOMin) (n p : ℕ)
    (hP1 : Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PYLip p n)) :
    ∀ C : ℝ, 1 ≤ C →
      Work.WilkG4c.FLemP S p (n + 1)
        (fun r k F => Work.WilkG4c.PY p n r k F ∧ Work.WilkG4c.LipOnCube F C) := by
  intro C hC1
  rw [FLemP_iff] at hP1
  rw [FLemP_iff]
  intro F0
  obtain ⟨K01, hfam⟩ := Work.WilG4c.FamGraphRescale S p n
  obtain ⟨K02, hchart⟩ := Work.WilG4c.ChartRescaleMem S p n
  obtain ⟨a', b', c', hmain⟩ := hP1 (F0 + K01)
  obtain ⟨M, hM⟩ := exists_nat_ge C
  have hM1 : C ≤ (((M + 1 : ℕ)) : ℝ) := by
    have : (((M + 1 : ℕ)) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
    linarith
  have hKpos : (0 : ℝ) < (((M + 1 : ℕ)) : ℝ) := by positivity
  obtain ⟨b, hb⟩ := Work.WilG4c.ShiftB b'
  obtain ⟨c, hc⟩ := Work.WilG4c.ShiftC c' ((M + 1) ^ (n + 1))
  refine ⟨a' + K02, b, c, ?_⟩
  intro D r k ε hε0 hε1 Λ F hP hΩ hval
  obtain ⟨hY, hLip⟩ := hP
  have hcorner0 : ∀ (j : Fin (n + 1) → Fin (M + 1)) (b : Fin (n + 1)), 0 ≤ tileQ M j b := by
    intro j b
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hcorner1 : ∀ (j : Fin (n + 1) → Fin (M + 1)) (b : Fin (n + 1)),
      tileQ M j b + 1 / (((M + 1 : ℕ)) : ℝ) ≤ 1 := by
    intro j b
    have hb_lt : (j b : ℕ) + 1 ≤ M + 1 := by
      have := (j b).isLt; omega
    have hsplit : tileQ M j b + 1 / (((M + 1 : ℕ)) : ℝ) =
        (((j b : ℕ) : ℝ) + 1) / (((M + 1 : ℕ)) : ℝ) := by
      simp only [tileQ]
      rw [add_div]
    rw [hsplit, div_le_one hKpos]
    exact_mod_cast hb_lt
  -- one rescaled family per tile of the grid
  have htile : ∀ j : Fin (n + 1) → Fin (M + 1),
      ∃ Ψ : Finset (ChartTuple p (n + 1)),
        ((Ψ.card : ℝ) ≤ MvPolynomial.eval
            ![((D + 2 : ℕ) : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] c' ∧
          ChartsOK S a' (MvPolynomial.eval ![D + 2, r] b') r Λ (tileFam M j F) Ψ ∧
          Covers Λ (tileFam M j F) Ψ (ε / 2)) := by
    intro j
    have hres : YBound (tileFam M j F) r ∧ LipOnCube (tileFam M j F) 1 ∧
        ValuesIn01 Λ (tileFam M j F) :=
      Work.WilG4c.RescalePredicates (k := k) n p (M + 1) (by omega) (tileQ M j)
        (hcorner0 j) (hcorner1 j) F r C hC1 hM1 Λ hY hLip hval
    obtain ⟨Ψ, hcard, hcharts, hcov⟩ := hmain (D + 2) r k (ε / 2) (by linarith) (by linarith)
      Λ (tileFam M j F) ⟨hres.1, hres.2.1⟩
      (fun i => hfam (M + 1) (tileQ M j) F0 D (F i) (hΩ i)) hres.2.2
    exact ⟨Ψ, hcard, hcharts, hcov⟩
  let Ψ : (Fin (n + 1) → Fin (M + 1)) → Finset (ChartTuple p (n + 1)) :=
    fun j => Classical.choose (htile j)
  have hΨcard : ∀ j : Fin (n + 1) → Fin (M + 1), ((Ψ j).card : ℝ) ≤
      MvPolynomial.eval ![((D + 2 : ℕ) : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] c' :=
    fun j => (Classical.choose_spec (htile j)).1
  have hΨcharts : ∀ j : Fin (n + 1) → Fin (M + 1),
      ChartsOK S a' (MvPolynomial.eval ![D + 2, r] b') r Λ (tileFam M j F) (Ψ j) :=
    fun j => (Classical.choose_spec (htile j)).2.1
  have hΨcov : ∀ j : Fin (n + 1) → Fin (M + 1),
      Covers Λ (tileFam M j F) (Ψ j) (ε / 2) :=
    fun j => (Classical.choose_spec (htile j)).2.2
  let emb : (Fin (n + 1) → Fin (M + 1)) → ChartTuple p (n + 1) ↪ ChartTuple p (n + 1) :=
    fun j => chartEmb (M + 1) (Nat.succ_pos M) (tileQ M j)
  let Φ : Finset (ChartTuple p (n + 1)) := Finset.univ.biUnion (fun j => (Ψ j).map (emb j))
  have hΦmem : ∀ φ : ChartTuple p (n + 1), φ ∈ Φ ↔
      ∃ j : Fin (n + 1) → Fin (M + 1), ∃ ψ ∈ Ψ j,
        φ = fun s l t => tileQ M j s + ψ s l t / (((M + 1 : ℕ)) : ℝ) := by
    intro φ
    constructor
    · intro hφ
      rw [show Φ = Finset.univ.biUnion (fun j => (Ψ j).map (emb j)) from rfl] at hφ
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_map] at hφ
      obtain ⟨j, ψ, hψ, heq⟩ := hφ
      refine ⟨j, ψ, hψ, ?_⟩
      rw [← heq]
      rfl
    · rintro ⟨j, ψ, hψ, rfl⟩
      rw [show Φ = Finset.univ.biUnion (fun j => (Ψ j).map (emb j)) from rfl]
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_map]
      exact ⟨j, ψ, hψ, rfl⟩
  refine ⟨Φ, ?_, ?_, ?_⟩
  · -- the cardinality bound
    have h1 : Φ.card ≤ ∑ j : Fin (n + 1) → Fin (M + 1), (Ψ j).card := by
      have hble : (Finset.univ.biUnion fun j => (Ψ j).map (emb j)).card ≤
          ∑ j ∈ (Finset.univ : Finset (Fin (n + 1) → Fin (M + 1))),
            ((Ψ j).map (emb j)).card :=
        Finset.card_biUnion_le
      calc Φ.card = (Finset.univ.biUnion fun j => (Ψ j).map (emb j)).card := rfl
        _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin (n + 1) → Fin (M + 1))),
              ((Ψ j).map (emb j)).card := hble
        _ = ∑ j : Fin (n + 1) → Fin (M + 1), ((Ψ j).map (emb j)).card := by simp
        _ = ∑ j : Fin (n + 1) → Fin (M + 1), (Ψ j).card :=
            Finset.sum_congr rfl (fun j _ => Finset.card_map (emb j))
    have h2 : ((∑ j : Fin (n + 1) → Fin (M + 1), (Ψ j).card : ℕ) : ℝ) ≤
        ∑ _j : Fin (n + 1) → Fin (M + 1),
          MvPolynomial.eval ![((D + 2 : ℕ) : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] c' := by
      rw [Nat.cast_sum]
      exact Finset.sum_le_sum (fun j _ => hΨcard j)
    have h3 : (∑ _j : Fin (n + 1) → Fin (M + 1),
          MvPolynomial.eval ![((D + 2 : ℕ) : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] c') =
        ((Fintype.card (Fin (n + 1) → Fin (M + 1)) : ℕ) : ℝ) *
          MvPolynomial.eval ![((D + 2 : ℕ) : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] c' := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h3' : ((Fintype.card (Fin (n + 1) → Fin (M + 1)) : ℕ) : ℝ) *
          MvPolynomial.eval ![((D + 2 : ℕ) : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] c' =
        (((M + 1) ^ (n + 1) : ℕ) : ℝ) *
          MvPolynomial.eval ![((D + 2 : ℕ) : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] c' := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    have h4 := hc D r k ε hε0 hε1
    calc (Φ.card : ℝ) ≤ ((∑ j : Fin (n + 1) → Fin (M + 1), (Ψ j).card : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ ≤ _ := h2
      _ = _ := h3
      _ = _ := h3'
      _ ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c := h4
  · -- the chart conditions
    intro φ hφ
    rw [hΦmem φ] at hφ
    obtain ⟨j, ψ, hψ, rfl⟩ := hφ
    have hchartsφ := hΨcharts j ψ hψ
    obtain ⟨hgr, hrest⟩ := hchartsφ
    refine ⟨?_, ?_⟩
    · intro s
      have hsrc := hgr s
      have hstep := hchart (K := M + 1) (c := tileQ M j s) (a := a')
        (Dg := MvPolynomial.eval ![D + 2, r] b') (ψ := ψ s) hsrc
      show famGraph (fun l t => tileQ M j s + ψ s l t / (((M + 1 : ℕ)) : ℝ)) ∈
        S.Ω (a' + K02) (MvPolynomial.eval ![D, r] b) (p + (n + 1) + 1)
      exact Omega_mono_le S le_rfl (le_of_eq (hb D r).symm) hstep
    · intro l hl
      obtain ⟨hcube, hsmooth⟩ := hrest l hl
      refine ⟨?_, ?_⟩
      · intro t ht s
        have hs := hcube t ht s
        have h0 := hcorner0 j s
        have h1 := hcorner1 j s
        show tileQ M j s + ψ s l t / (((M + 1 : ℕ)) : ℝ) ∈ Set.Ioo (0 : ℝ) 1
        constructor
        · have h2 : 0 < ψ s l t / (((M + 1 : ℕ)) : ℝ) := div_pos hs.1 hKpos
          linarith
        · have h2 : ψ s l t / (((M + 1 : ℕ)) : ℝ) < 1 / (((M + 1 : ℕ)) : ℝ) :=
            div_lt_div_of_pos_right hs.2 hKpos
          linarith
      · intro i
        obtain ⟨hcd, hder⟩ := hsmooth i
        have hfun : (fun t => tileFam M j F i l (fun s => ψ s l t)) =
            (fun t => F i l (fun j_1 =>
              (fun s l t => tileQ M j s + ψ s l t / (((M + 1 : ℕ)) : ℝ)) j_1 l t)) := rfl
        refine ⟨?_, ?_⟩
        · rw [← hfun]; exact hcd
        · intro m hm t ht
          rw [← hfun]
          exact hder m hm t ht
  · -- the cover
    exact Work.WilG4c.TileCover n (M + 1) (by omega) C hC1 hM1 Λ F hLip ε hε0 hε1 Ψ
      (fun j => hΨcov j) Φ (fun φ => hΦmem φ)

end Work.WilG4c
