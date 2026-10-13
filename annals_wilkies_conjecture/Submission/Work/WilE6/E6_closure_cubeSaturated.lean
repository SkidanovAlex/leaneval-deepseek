import Mathlib
import Submission.Work.WilE6.Closure
import Submission.Work.WilE6.CritSA
import Submission.Work.WilE6.Base
import Submission.Work.WilE6.Block
import Submission.Work.WilE6.Setup
import Submission.Work.WilE6.critSA_mem_iff
import Submission.Work.WilE6.critSA_deg_le
import Submission.Work.WilE6.mem_saSlice_iff
import Submission.Work.WilE6.eaTaylor_poly_shifted
import Submission.Work.WilE6.norm_witness_iff
import Submission.Work.WilE6.critFibreCond_imp_critCond
import Submission.Work.WilE6.critCond_imp_exists_witness
import Submission.Work.WilE6.FrozenCrit
import Submission.Work.WilE6.CritAssemble
import Submission.Work.WilE6.Main

noncomputable section
namespace Work.WilE6
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

theorem E6_closure_cubeSaturated (hE3b : ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : WilkiesDesign.E.EAChain k r) (B : WilkiesDesign.E.Basic k r) (y : Fin k → ℝ) (κ : ℕ), k + r ≤ F → K.eval B.deg < κ → (y ∈ closure {x | B.holds c x} ↔ y ∈ closure {x | (∀ f ∈ B.eqs, |WilkiesDesign.E.eaTaylor c f (κ ^ 2) y x| ≤ dist x y ^ (κ ^ 2)) ∧ (∀ g ∈ B.pos, dist x y ^ κ < WilkiesDesign.E.eaTaylor c g κ y x)})) (hE4 : ∀ p q : ℕ, ∃ b : Polynomial ℕ, ∀ X : WilkiesDesign.E.SA (p + q), ∃ Y : WilkiesDesign.E.SA (p + q), Y.deg ≤ b.eval X.deg ∧ Y.set = WilkiesDesign.E.fiberClosure X.set) (F : ℕ) : ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F → (∀ B ∈ X.basics, ∀ z : Fin (p + q) → ℝ, B.holds X.c z → z ∈ WilkiesDesign.E.cubeC (p + q)) → ∃ Y : WilkiesDesign.E.SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y.set = WilkiesDesign.E.fiberClosure X.set := by
  obtain ⟨K, hK⟩ := hE3b F
  obtain ⟨Q, hQ⟩ := critUnion_deg_le K F
  let b4 : Polynomial ℕ :=
    ∑ u ∈ Finset.range (F + 1), ∑ v ∈ Finset.range (4 * F + 5), (hE4 u v).choose
  have hb4 : ∀ u v : ℕ, u ≤ F → v ≤ 4 * F + 4 → ∀ Y : SA (u + v),
      ∃ Z : SA (u + v), Z.deg ≤ b4.eval Y.deg ∧ Z.set = fiberClosure Y.set := by
    intro u v hu hv Y
    obtain ⟨Z, hZdeg, hZset⟩ := (hE4 u v).choose_spec Y
    refine ⟨Z, hZdeg.trans ?_, hZset⟩
    have h1 : ((hE4 u v).choose).eval Y.deg ≤
        (∑ v' ∈ Finset.range (4 * F + 5), (hE4 u v').choose).eval Y.deg := by
      rw [Polynomial.eval_finsetSum]
      have hv' : v ∈ Finset.range (4 * F + 5) := Finset.mem_range.mpr (by omega)
      exact Finset.single_le_sum (s := Finset.range (4 * F + 5))
        (f := fun v' => ((hE4 u v').choose).eval Y.deg) (fun _ _ => Nat.zero_le _) hv'
    have h2 : (∑ v' ∈ Finset.range (4 * F + 5), (hE4 u v').choose).eval Y.deg ≤
        b4.eval Y.deg := by
      rw [show b4 = ∑ u' ∈ Finset.range (F + 1),
          ∑ v' ∈ Finset.range (4 * F + 5), (hE4 u' v').choose from rfl]
      conv_rhs => rw [Polynomial.eval_finsetSum]
      have hu' : u ∈ Finset.range (F + 1) := Finset.mem_range.mpr (by omega)
      exact Finset.single_le_sum (s := Finset.range (F + 1))
        (f := fun x => (∑ v' ∈ Finset.range (4 * F + 5), (hE4 x v').choose).eval Y.deg)
        (fun _ _ => Nat.zero_le _) hu'
    exact h1.trans h2
  refine ⟨F, b4.comp Q, ?_⟩
  intro p q X hfmt hsat
  rcases Nat.eq_zero_or_pos (p + q) with h0 | hpos
  · have hp0 : p = 0 := by omega
    have hq0 : q = 0 := by omega
    subst hp0
    subst hq0
    have hfc : fiberClosure X.set = X.set := by
      show fiberClosure (p := 0) (q := 0) X.set = X.set
      exact fiberClosure_zero X
    have huniq : ∀ z : Fin (0 + 0) → ℝ, z = (0 : Fin (0 + 0) → ℝ) :=
      fun z => by funext i; exact i.elim0
    by_cases hne : ∃ B ∈ X.basics, B.holds X.c (0 : Fin (0 + 0) → ℝ)
    · refine ⟨⟨X.r, X.c, [⟨[], []⟩]⟩, ?_, ?_, ?_⟩
      · show (0 : ℕ) + X.r ≤ F
        have := hfmt
        simp only [SemiPf.fmt] at this
        omega
      · have hdeg0 : (⟨X.r, X.c, [⟨[], []⟩]⟩ : SemiPf (0 + 0)).deg = 0 := rfl
        rw [hdeg0]
        exact Nat.zero_le _
      · rw [hfc]
        ext z
        constructor
        · intro _
          obtain ⟨B, hB, hBh⟩ := hne
          refine ⟨?_, B, hB, ?_⟩
          · intro i; exact i.elim0
          · rwa [huniq z]
        · intro _
          exact ⟨(by intro i; exact i.elim0), ⟨[], []⟩, List.mem_singleton.mpr rfl,
            by simp [Basic.holds]⟩
    · refine ⟨⟨X.r, X.c, []⟩, ?_, ?_, ?_⟩
      · show (0 : ℕ) + X.r ≤ F
        have := hfmt
        simp only [SemiPf.fmt] at this
        omega
      · have hdeg0 : (⟨X.r, X.c, []⟩ : SemiPf (0 + 0)).deg = 0 := rfl
        rw [hdeg0]
        exact Nat.zero_le _
      · rw [hfc]
        ext z
        constructor
        · intro hz
          obtain ⟨-, B, hB, -⟩ := hz
          exact absurd hB (by simp)
        · intro hz
          exfalso
          obtain ⟨-, B, hB, hBh⟩ := hz
          exact hne ⟨B, hB, by simpa [huniq z] using hBh⟩
  · have hpF : p ≤ F := by
      have := hfmt; simp only [SemiPf.fmt] at this; omega
    have hpqF : p + q ≤ F := by
      have := hfmt; simp only [SemiPf.fmt] at this; omega
    have hBP : BP (p + q) X.r ≤ F := hfmt
    have hFQ : FQ (p + q) p ≤ 4 * F + 4 := by simp only [FQ]; omega
    have hlen : X.basics.length ≤ X.deg := by
      have h1 : ∀ B ∈ X.basics, 1 ≤ B.deg := fun B hB => one_le_deg_of_cubesat hpos hsat hB
      have hconst : (X.basics.map (fun _ => (1 : ℕ))).sum = X.basics.length := by
        rw [sum_map_const]; omega
      rw [← hconst]
      show (X.basics.map (fun _ => (1 : ℕ))).sum ≤ (X.basics.map Basic.deg).sum
      exact List.sum_le_sum (fun B hB => h1 B hB)
    obtain ⟨Z4, hZ4deg, hZ4set⟩ :=
      hb4 (BP (p + q) X.r) (FQ (p + q) p) hBP hFQ (critUnionOf K X)
    have hdegOf : ∀ (z : Fin (p + q) → ℝ) (B : Basic (p + q) X.r), B ∈ X.basics →
        K.eval (frozenBasic p q X.r B z).deg < kappa K X.deg p := by
      intro z B hB
      have hBD : B.deg ≤ X.deg := deg_le_sum hB
      rw [kappa]
      have h3 : (frozenBasic p q X.r B z).deg ≤ 3 * X.deg + 2 * p + 1 :=
        (frozenBasic_deg_le (r := X.r) B z).trans (by omega)
      exact Nat.lt_succ_of_le (polynomial_eval_mono K h3)
    refine ⟨saPullback X.c (saSlice (BP (p + q) X.r) (FQ (p + q) p) Z4), ?_, ?_, ?_⟩
    · show (p + q) + X.r ≤ F
      exact hfmt
    · refine (saPullback_deg_le X.c _).trans ?_
      refine (saSlice_deg_le _ _ Z4).trans ?_
      refine hZ4deg.trans ?_
      refine (polynomial_eval_mono b4 (hQ p q X hfmt hlen)).trans ?_
      rw [Polynomial.eval_comp]
    · have hUx : critUnionOf K X =
          critUnion (p := p) (by omega : p ≤ p + q) (kappa K X.deg p) X := rfl
      ext z
      rw [show z ∈ (saPullback X.c (saSlice (BP (p + q) X.r) (FQ (p + q) p) Z4)).set ↔
            z ∈ cubeC (p + q) ∧
              gpBP X.c z ∈ (saSlice (BP (p + q) X.r) (FQ (p + q) p) Z4).set
          from mem_saPullback_iff X.c (saSlice (BP (p + q) X.r) (FQ (p + q) p) Z4) z]
      have hkey : (Fin.append (gpBP X.c z) (0 : Fin (FQ (p + q) p) → ℝ) ∈
            fiberClosure (critUnionOf K X).set) ↔ z ∈ fiberClosure X.set := by
        rw [hUx, mem_fiberClosure_iff, projFirst_append, projSnd_append,
          mem_fiberClosure_iff]
        have h1 : (∃ B ∈ X.basics,
              projSnd p q z ∈ closure (fiber (B.holds X.c) (projFirst p q z)))
            ↔ projSnd p q z ∈ closure (fiber X.set (projFirst p q z)) := by
          rw [fiber_set_eq X hsat (projFirst p q z), closure_listUnion, List.map_map,
            mem_listUnion]
          constructor
          · rintro ⟨B, hB, h⟩
            exact ⟨closure (fiber (B.holds X.c) (projFirst p q z)),
              List.mem_map.mpr ⟨B, hB, rfl⟩, h⟩
          · rintro ⟨S, hS, h⟩
            obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hS
            exact ⟨B, hB, h⟩
        rw [fiber_critUnion_eq (p := p) (by omega : p ≤ p + q) (kappa K X.deg p) X z,
          closure_listUnion, List.map_map, mem_listUnion, ← h1]
        constructor
        · rintro ⟨S, hS, h0⟩
          obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hS
          exact ⟨B, hB, (perB_iff K F hK (by omega : p ≤ p + q) X B z hfmt
            (hdegOf z B hB)).mp h0⟩
        · rintro ⟨B, hB, hB2⟩
          refine ⟨closure (uSet (r := X.r) (by omega : p ≤ p + q) (kappa K X.deg p) X.c B z),
            List.mem_map.mpr ⟨B, hB, rfl⟩, ?_⟩
          exact (perB_iff K F hK (by omega : p ≤ p + q) X B z hfmt (hdegOf z B hB)).mpr hB2
      constructor
      · rintro ⟨-, hz⟩
        rw [mem_saSlice_iff] at hz
        rw [hZ4set] at hz
        exact hkey.mp hz
      · intro hz
        have hz'' : projSnd p q z ∈ closure (fiber X.set (projFirst p q z)) := by
          rwa [mem_fiberClosure_iff] at hz
        refine ⟨?_, ?_⟩
        · have hsub := closure_fiber_subset_cube (S := X.set) (fun w hw => hw.1) hz''
          rw [Set.mem_preimage] at hsub
          rwa [fin_append_projFirst_projSnd] at hsub
        · rw [mem_saSlice_iff, hZ4set]
          exact hkey.mpr hz

end Work.WilE6
