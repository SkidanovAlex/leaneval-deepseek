import Mathlib
import Submission.Work.Q44Geom.Setup
import Submission.Work.Q44Geom.Basic
import Submission.Work.Q44Geom.BadDefs
import Submission.Work.Q44Geom.invSub_finrank_le
import Submission.Work.Q44Geom.class_rep
import Submission.Work.Q44Geom.badA_subset
import Submission.Work.Q44Geom.bad_fiber_count
import Submission.Work.Q44Geom.exists_gen_pair_lam
import Submission.Work.HP.MDBasic.finite_sets

/-!
# `Work.Q44Geom.bad_count`

The number of `L ∈ Sset c s` with *no* good pair is `≪ s 0 ^ 3 * s 1 ^ 5 * s 2 ^ 2`, uniformly
in `c` and `s`.

The bad lattices `L` are split according to the rank of `N_L := L ⊓ latW (f44 c)`:

* if `rk N_L = 3`, then `L = N_L = W` is the invariance lattice itself, so there is at most one
  such `L` (`badA_subset`);
* if `rk N_L = 2`, then `L` is determined by the rank-`2` lattice `N_L` together with the class
  of a short generator of `L` over `N_L` (which exists by `class_rep` and `gen_of_le`).

The possible `N_L` are counted by their canonical generating pair (`exists_gen_pair_lam`) inside
the two balls of `latW` of radii `s 0` and `s 1` (`latW_count_uniform`), and for each fixed `N`
the number of `L` is bounded by `bad_fiber_count`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Q44Geom

open MvPolynomial

/-! ## The main theorem -/

theorem bad_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : Work.HP.Mon 4 4 → ℤ), Work.HP.formOf 4 4 c ≠ 0 →
      Irreducible (Work.HP.formOf 4 4 c) → ∀ (s : Fin 3 → ℝ), 1 ≤ s 0 → s 0 ≤ s 1 → s 1 ≤ s 2 →
      (({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ Work.Q44Geom.Sset c s ∧
        ¬ Work.Q44Geom.goodPair c s L} : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
        ≤ C * (s 0) ^ 3 * (s 1) ^ 5 * (s 2) ^ 2 := by
  classical
  obtain ⟨C_F, hC_Fpos, hC_F⟩ := bad_fiber_count
  obtain ⟨C_W, hC_Wpos, hC_W⟩ := latW_count_uniform
  obtain ⟨C_P, hC_Ppos, hC_P⟩ := exists_gen_pair_lam
  obtain ⟨C_rep, hC_reppos, hC_rep⟩ := class_rep
  let Cp : ℝ := max C_P 1
  have hCp1 : 1 ≤ Cp := le_max_right _ _
  have hCppos : 0 < Cp := lt_of_lt_of_le zero_lt_one hCp1
  have hCPCp : C_P ≤ Cp := le_max_left _ _
  refine ⟨64 * C_W ^ 2 * Cp ^ 6 * C_F + 1, by positivity, ?_⟩
  intro c hf0 hfirr s hs1 hs01 hs12
  show ((Work.Q44Geom.badSet c s : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
      ≤ (64 * C_W ^ 2 * Cp ^ 6 * C_F + 1) * s 0 ^ 3 * s 1 ^ 5 * s 2 ^ 2
  have hs0 : (0 : ℝ) ≤ s 0 := le_trans zero_le_one hs1
  have hs1' : (0 : ℝ) ≤ s 1 := le_trans hs0 hs01
  have hs2' : (0 : ℝ) ≤ s 2 := le_trans hs1' hs12
  set W : Submodule ℤ (Fin 5 → ℤ) := Wlat c with hWdef
  have hWprim : Work.HP.IsPrimLat W := isPrimLat_Wlat c
  have hWrk : Work.HP.rk W ≤ 3 := le_trans (latW_rank_le (f44 c)) (invSub_finrank_le c hf0 hfirr)
  -- ### Rank bounds for `L ⊓ W` when `L` is bad
  have hrk_low : ∀ L ∈ badSet c s, 2 ≤ Work.HP.rk (L ⊓ W) := by
    intro L hL
    obtain ⟨hLs, hLngp⟩ := hL
    obtain ⟨x, y, hx, hy, hxl, hyl, hind⟩ := bad_structure hLs hLngp
    exact two_le_rk_of_linIndep (Submodule.mem_inf.mpr ⟨hx, hxl⟩)
      (Submodule.mem_inf.mpr ⟨hy, hyl⟩) hind
  have hrk_high : ∀ L ∈ badSet c s, Work.HP.rk (L ⊓ W) ≤ 3 := by
    intro L hL
    obtain ⟨hLs, -⟩ := hL
    have h1 : Module.finrank ℚ (ratSpan (L ⊓ W)) ≤ Module.finrank ℚ (ratSpan L) :=
      Submodule.finrank_mono (ratSpan_mono inf_le_left)
    rw [ratSpan_finrank_general (L ⊓ W), ratSpan_finrank_general L, hLs.2.1] at h1
    exact h1
  have hlam_mem : ∀ L ∈ badSet c s, Work.HP.lam (L ⊓ W) 2 ≤ s 1 := by
    intro L hL
    obtain ⟨hLs, hLngp⟩ := hL
    obtain ⟨x, y, hxN, hyN, hind, hnx, hny⟩ := short_pair_in_Nof hLs hLngp
    exact le_trans (Work.HP.lam_two_le_max (L ⊓ W) hxN hyN hind)
      (max_le (le_trans hnx hs01) hny)
  have hlam1_mem : ∀ L ∈ badSet c s, Work.HP.lam (L ⊓ W) 1 ≤ s 0 := by
    intro L hL
    obtain ⟨hLs, hLngp⟩ := hL
    obtain ⟨x, y, hxN, hyN, hind, hnx, hny⟩ := short_pair_in_Nof hLs hLngp
    have hx0 : x ≠ 0 := hind.ne_zero (0 : Fin 2)
    exact le_trans (Work.HP.lam_one_le_eNorm (L ⊓ W) hxN hx0) hnx
  -- ### The two pieces of the bad set
  have hcover : badSet c s ⊆ badASet c s ∪ bad2Set c s := by
    intro L hL
    have h2 := hrk_low L hL
    have h3 := hrk_high L hL
    have hcases : Work.HP.rk (L ⊓ W) = 2 ∨ Work.HP.rk (L ⊓ W) = 3 := by omega
    rcases hcases with h | h
    · right; exact ⟨hL, h⟩
    · left; exact ⟨hL, h⟩
  have hBadA_sub : badASet c s ⊆ {W} := by
    intro L hL
    have h := badA_subset c hf0 hfirr s hL
    simpa [hWdef] using h
  have hBadA_fin : (badASet c s).Finite := (Set.finite_singleton W).subset hBadA_sub
  have hBadA_le : (badASet c s).ncard ≤ 1 := by
    have h1 : (badASet c s).ncard ≤ ({W} : Set (Submodule ℤ (Fin 5 → ℤ))).ncard :=
      Set.ncard_le_ncard hBadA_sub (Set.finite_singleton W)
    simpa using h1
  -- ### The canonical generating pair of a rank-`2` lattice
  have hpair_exists : ∀ N : Submodule ℤ (Fin 5 → ℤ), Work.HP.rk N = 2 →
      ∃ p : (Fin 5 → ℤ) × (Fin 5 → ℤ), p.1 ∈ N ∧ p.2 ∈ N ∧
        N = Submodule.span ℤ {p.1, p.2} ∧
        Work.HP.eNorm p.1 ≤ C_P * Work.HP.lam N 1 ∧
        Work.HP.eNorm p.2 ≤ C_P * Work.HP.lam N 2 := by
    intro N h
    obtain ⟨x, y, hx, hy, hsp, hb1, hb2⟩ := hC_P N h
    exact ⟨(x, y), hx, hy, hsp, hb1, hb2⟩
  let pairOf : (Submodule ℤ (Fin 5 → ℤ)) → (Fin 5 → ℤ) × (Fin 5 → ℤ) := fun N =>
    if h : Work.HP.rk N = 2 then Classical.choose (hpair_exists N h) else (0, 0)
  have hpairOf_spec : ∀ (N : Submodule ℤ (Fin 5 → ℤ)) (h : Work.HP.rk N = 2),
      (pairOf N).1 ∈ N ∧ (pairOf N).2 ∈ N ∧
        N = Submodule.span ℤ {(pairOf N).1, (pairOf N).2} ∧
        Work.HP.eNorm (pairOf N).1 ≤ C_P * Work.HP.lam N 1 ∧
        Work.HP.eNorm (pairOf N).2 ≤ C_P * Work.HP.lam N 2 := by
    intro N h
    have h1 := Classical.choose_spec (hpair_exists N h)
    dsimp only [pairOf]
    rw [dif_pos h]
    exact h1
  -- ### The finite set of pairs
  set PSet : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)) :=
    {p | p.1 ∈ W ∧ p.2 ∈ W ∧ Work.HP.eNorm p.1 ≤ Cp * s 0 ∧ Work.HP.eNorm p.2 ≤ Cp * s 1}
      with hPSetdef
  have hPSet_fin : PSet.Finite := by
    have h1 : PSet ⊆ ({v : Fin 5 → ℤ | Work.HP.eNorm v ≤ Cp * s 0} ×ˢ
        {v : Fin 5 → ℤ | Work.HP.eNorm v ≤ Cp * s 1}) := by
      intro p hp
      exact ⟨hp.2.2.1, hp.2.2.2⟩
    exact ((Work.HP.MDBasic.finite_eNorm_le (ι := Fin 5) (Cp * s 0)).prod
      (Work.HP.MDBasic.finite_eNorm_le (ι := Fin 5) (Cp * s 1))).subset h1
  have hPSet_mem : ∀ L ∈ bad2Set c s, pairOf (L ⊓ W) ∈ PSet := by
    intro L hL
    obtain ⟨hLbad, hrk⟩ := hL
    obtain ⟨hp1, hp2, -, hb1, hb2⟩ := hpairOf_spec (L ⊓ W) hrk
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (inf_le_right : L ⊓ W ≤ W) hp1
    · exact (inf_le_right : L ⊓ W ≤ W) hp2
    · calc Work.HP.eNorm (pairOf (L ⊓ W)).1 ≤ C_P * Work.HP.lam (L ⊓ W) 1 := hb1
        _ ≤ Cp * s 0 :=
            mul_le_mul hCPCp (hlam1_mem L hLbad) (Work.HP.lam_nonneg _ 1) hCppos.le
    · calc Work.HP.eNorm (pairOf (L ⊓ W)).2 ≤ C_P * Work.HP.lam (L ⊓ W) 2 := hb2
        _ ≤ Cp * s 1 :=
            mul_le_mul hCPCp (hlam_mem L hLbad) (Work.HP.lam_nonneg _ 2) hCppos.le
  -- ### Finiteness of the fibres
  have hfinN : ∀ N : Submodule ℤ (Fin 5 → ℤ),
      ({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ badSet c s ∧ L ⊓ W = N} :
        Set (Submodule ℤ (Fin 5 → ℤ))).Finite := by
    intro N
    by_cases hrkN : Work.HP.rk N = 2
    · set R : ℝ := 2 * C_rep * s 2 with hRdef
      let genEx : Submodule ℤ (Fin 5 → ℤ) → Prop := fun L =>
        ∃ z : Fin 5 → ℤ, z ∈ L ∧ (∀ w ∈ L, ∃ k : ℤ, ∃ n ∈ L ⊓ W, w = k • z + n) ∧
          Work.HP.eNorm z ≤ R
      let zOf : (Submodule ℤ (Fin 5 → ℤ)) → (Fin 5 → ℤ) :=
        fun L => if h : genEx L then Classical.choose h else 0
      have hzOf : ∀ L, genEx L → zOf L ∈ L ∧
          (∀ w ∈ L, ∃ k : ℤ, ∃ n ∈ L ⊓ W, w = k • (zOf L) + n) ∧ Work.HP.eNorm (zOf L) ≤ R := by
        intro L h
        have h1 : zOf L = Classical.choose h := by
          dsimp only [zOf]
          exact dif_pos h
        rw [h1]
        exact Classical.choose_spec h
      have hgen : ∀ L, L ∈ ({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ badSet c s ∧ L ⊓ W = N} :
          Set _) → genEx L := by
        intro L hL
        obtain ⟨⟨⟨hprim, hLrk, hlam, hv⟩, hLngp⟩, hLN⟩ := hL
        have hLbad : L ∈ badSet c s := ⟨⟨hprim, hLrk, hlam, hv⟩, hLngp⟩
        have hNprim : Work.HP.IsPrimLat N := by
          rw [← hLN]; exact isPrimLat_inf hprim (isPrimLat_Wlat c)
        obtain ⟨z₀, hz₀L, hz₀gen⟩ :=
          gen_of_le N L (by rw [← hLN]; exact inf_le_left) hNprim hrkN hLrk
        have hlamL3 : Work.HP.lam L 3 ≤ s 2 := by
          have h := hlam ⟨2, by norm_num⟩
          simpa using h
        obtain ⟨z, hzL, hzgen, hze⟩ :=
          hC_rep N L hNprim hprim (by rw [← hLN]; exact inf_le_left) hrkN hLrk
            ⟨z₀, hz₀L, hz₀gen⟩ (s 2) hlamL3
        refine ⟨z, hzL, ?_, ?_⟩
        · intro w hw
          obtain ⟨k, n, hn, hwn⟩ := hzgen w hw
          exact ⟨k, n, by rw [hLN]; exact hn, hwn⟩
        · refine le_trans hze ?_
          have h1 : Work.HP.lam N 2 ≤ s 2 := by
            rw [← hLN]
            exact le_trans (hlam_mem L hLbad) hs12
          have h2 : s 2 + Work.HP.lam N 2 ≤ 2 * s 2 := by linarith
          calc C_rep * (s 2 + Work.HP.lam N 2) ≤ C_rep * (2 * s 2) :=
                mul_le_mul_of_nonneg_left h2 hC_reppos.le
            _ = R := by rw [hRdef]; ring
      have hinj : Set.InjOn (fun L => zOf L)
          {L : Submodule ℤ (Fin 5 → ℤ) | L ∈ badSet c s ∧ L ⊓ W = N} := by
        intro L hL L' hL' hzz
        obtain ⟨hzL, hzgL, -⟩ := hzOf L (hgen L hL)
        obtain ⟨hzL', hzgL', -⟩ := hzOf L' (hgen L' hL')
        obtain ⟨-, hLN⟩ := hL
        obtain ⟨-, hLN'⟩ := hL'
        have hzz' : zOf L = zOf L' := hzz
        apply le_antisymm
        · intro w hw
          obtain ⟨k, n, hn, hwn⟩ := hzgL w hw
          have hnN : n ∈ N := by rw [← hLN]; exact hn
          have hn' : n ∈ L' := by
            have h2 : n ∈ L' ⊓ W := by rw [hLN']; exact hnN
            exact (inf_le_left : L' ⊓ W ≤ L') h2
          rw [hwn, hzz']
          exact L'.add_mem (L'.smul_mem k hzL') hn'
        · intro w hw
          obtain ⟨k, n, hn, hwn⟩ := hzgL' w hw
          have hnN : n ∈ N := by rw [← hLN']; exact hn
          have hn' : n ∈ L := by
            have h2 : n ∈ L ⊓ W := by rw [hLN]; exact hnN
            exact (inf_le_left : L ⊓ W ≤ L) h2
          rw [hwn, ← hzz']
          exact L.add_mem (L.smul_mem k hzL) hn'
      refine Set.Finite.of_injOn ?_ hinj (Work.HP.MDBasic.finite_eNorm_le (ι := Fin 5) R)
      intro L hL
      exact (hzOf L (hgen L hL)).2.2
    · have hsub : ({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ badSet c s ∧ L ⊓ W = N} : Set _)
          ⊆ {W} := by
        intro L hL
        obtain ⟨hLbad, hLN⟩ := hL
        rw [Set.mem_singleton_iff]
        have h2 := hrk_low L hLbad
        have h3 := hrk_high L hLbad
        have hrk3 : Work.HP.rk (L ⊓ W) = 3 := by
          rcases (by omega : Work.HP.rk (L ⊓ W) = 2 ∨ Work.HP.rk (L ⊓ W) = 3) with h | h
          · exact absurd (by rw [← hLN]; exact h) hrkN
          · exact h
        have h := badA_subset c hf0 hfirr s ⟨hLbad, hrk3⟩
        simpa [hWdef] using h
      exact (Set.finite_singleton W).subset hsub
  have hFfin : ∀ p : (Fin 5 → ℤ) × (Fin 5 → ℤ),
      ({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ bad2Set c s ∧ pairOf (L ⊓ W) = p} :
        Set (Submodule ℤ (Fin 5 → ℤ))).Finite := by
    intro p
    refine (hfinN (Submodule.span ℤ {p.1, p.2})).subset ?_
    intro L hL
    obtain ⟨hLbad2, hLp⟩ := hL
    obtain ⟨-, -, hspan, -, -⟩ := hpairOf_spec (L ⊓ W) hLbad2.2
    exact ⟨hLbad2.1, by rw [hspan, hLp]⟩
  -- ### The fibre bound
  have hfib_bound : ∀ p ∈ PSet,
      (({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ bad2Set c s ∧ pairOf (L ⊓ W) = p} :
        Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) ≤ C_F * s 1 ^ 2 * s 2 ^ 2 := by
    intro p hp
    by_cases hne : ({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ bad2Set c s ∧ pairOf (L ⊓ W) = p} :
        Set (Submodule ℤ (Fin 5 → ℤ))).Nonempty
    · obtain ⟨L₀, hL₀⟩ := hne
      obtain ⟨hL₀bad2, hL₀pair⟩ := hL₀
      obtain ⟨hL₀bad, hrk₀⟩ := hL₀bad2
      have hNprim : Work.HP.IsPrimLat (L₀ ⊓ W) := by
        obtain ⟨hL₀s, -⟩ := hL₀bad
        exact isPrimLat_inf hL₀s.1 (isPrimLat_Wlat c)
      have hbf := hC_F c hf0 (formOf_totalDegree_le 4 4 c) s hs1 hs01 hs12 (L₀ ⊓ W)
        hNprim hrk₀ (hlam_mem L₀ hL₀bad)
      have hsub : ({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ bad2Set c s ∧ pairOf (L ⊓ W) = p} :
          Set _) ⊆ ({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ Sset c s ∧ ¬ goodPair c s L ∧
            L ⊓ W = L₀ ⊓ W} : Set _) := by
        intro L hL
        obtain ⟨hLbad2, hLp⟩ := hL
        obtain ⟨hLbad, hrkL⟩ := hLbad2
        obtain ⟨hLs, hLngp⟩ := hLbad
        obtain ⟨-, -, hLspan, -, -⟩ := hpairOf_spec (L ⊓ W) hrkL
        obtain ⟨-, -, hL₀span, -, -⟩ := hpairOf_spec (L₀ ⊓ W) hrk₀
        refine ⟨hLs, hLngp, ?_⟩
        rw [hLspan, hL₀span, hLp, hL₀pair]
      have hfin : ({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ Sset c s ∧ ¬ goodPair c s L ∧
          L ⊓ W = L₀ ⊓ W} : Set _).Finite :=
        (hfinN (L₀ ⊓ W)).subset (fun L hL => ⟨⟨hL.1, hL.2.1⟩, hL.2.2⟩)
      have hnb : (({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ bad2Set c s ∧ pairOf (L ⊓ W) = p} :
            Set _).ncard : ℝ)
          ≤ (({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ Sset c s ∧ ¬ goodPair c s L ∧
              L ⊓ W = L₀ ⊓ W} : Set _).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub hfin
      calc (({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ bad2Set c s ∧ pairOf (L ⊓ W) = p} :
            Set _).ncard : ℝ)
          ≤ (({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ Sset c s ∧ ¬ goodPair c s L ∧
              L ⊓ W = L₀ ⊓ W} : Set _).ncard : ℝ) := hnb
        _ ≤ C_F * s 1 ^ 2 * s 2 ^ 2 := hbf
    · have h0 : ({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ bad2Set c s ∧ pairOf (L ⊓ W) = p} :
          Set _) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      rw [h0, Set.ncard_empty, Nat.cast_zero]
      positivity
  -- ### Counting the fibres
  have hBad2_sub : bad2Set c s ⊆ ⋃ p ∈ PSet,
      ({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ bad2Set c s ∧ pairOf (L ⊓ W) = p} : Set _) := by
    intro L hL
    simp only [Set.mem_iUnion]
    exact ⟨pairOf (L ⊓ W), hPSet_mem L hL, hL, rfl⟩
  have hBad2_fin : (bad2Set c s).Finite :=
    (hPSet_fin.biUnion (fun p _ => hFfin p)).subset hBad2_sub
  have hcard : hBad2_fin.toFinset.card =
      ∑ p ∈ hPSet_fin.toFinset,
        (hBad2_fin.toFinset.filter (fun L => pairOf (L ⊓ W) = p)).card :=
    Finset.card_eq_sum_card_fiberwise (s := hBad2_fin.toFinset) (t := hPSet_fin.toFinset)
      (f := fun L => pairOf (L ⊓ W)) (fun L hL => by
        rw [Finset.mem_coe] at hL
        rw [Finset.mem_coe, hPSet_fin.mem_toFinset]
        exact hPSet_mem L (hBad2_fin.mem_toFinset.mp hL))
  have hBad2_le : ((bad2Set c s).ncard : ℝ) ≤
      (PSet.ncard : ℝ) * (C_F * s 1 ^ 2 * s 2 ^ 2) := by
    have hterm : ∀ p ∈ hPSet_fin.toFinset,
        (((hBad2_fin.toFinset.filter (fun L => pairOf (L ⊓ W) = p)).card : ℕ) : ℝ)
          ≤ C_F * s 1 ^ 2 * s 2 ^ 2 := by
      intro p hp
      have hp' : p ∈ PSet := hPSet_fin.mem_toFinset.mp hp
      have h1 : (((hBad2_fin.toFinset.filter (fun L => pairOf (L ⊓ W) = p)).card : ℕ) : ℝ)
          ≤ (({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ bad2Set c s ∧ pairOf (L ⊓ W) = p} :
              Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) := by
        have hsub : ((hBad2_fin.toFinset.filter (fun L => pairOf (L ⊓ W) = p)) : Set _)
            ⊆ ({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ bad2Set c s ∧ pairOf (L ⊓ W) = p} :
              Set (Submodule ℤ (Fin 5 → ℤ))) := by
          intro L hL
          rw [Finset.mem_coe, Finset.mem_filter] at hL
          exact ⟨hBad2_fin.mem_toFinset.mp hL.1, hL.2⟩
        have h2 := Set.ncard_le_ncard hsub (hFfin p)
        rw [Set.ncard_coe_finset] at h2
        exact_mod_cast h2
      exact le_trans h1 (hfib_bound p hp')
    calc ((bad2Set c s).ncard : ℝ) = ((hBad2_fin.toFinset.card : ℕ) : ℝ) := by
          rw [Set.ncard_eq_toFinset_card (bad2Set c s) hBad2_fin]
      _ = ∑ p ∈ hPSet_fin.toFinset,
            (((hBad2_fin.toFinset.filter (fun L => pairOf (L ⊓ W) = p)).card : ℕ) : ℝ) := by
          rw [hcard]
          push_cast
          rfl
      _ ≤ ∑ p ∈ hPSet_fin.toFinset, (C_F * s 1 ^ 2 * s 2 ^ 2) := Finset.sum_le_sum hterm
      _ = (hPSet_fin.toFinset.card : ℝ) * (C_F * s 1 ^ 2 * s 2 ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (PSet.ncard : ℝ) * (C_F * s 1 ^ 2 * s 2 ^ 2) := by
          rw [Set.ncard_eq_toFinset_card PSet hPSet_fin]
  -- ### The number of pairs
  have hPSet_le : (PSet.ncard : ℝ) ≤ 64 * C_W ^ 2 * Cp ^ 6 * s 0 ^ 3 * s 1 ^ 3 := by
    have hprod : PSet = ({v : Fin 5 → ℤ | v ∈ W ∧ Work.HP.eNorm v ≤ Cp * s 0} :
          Set (Fin 5 → ℤ))
        ×ˢ ({v : Fin 5 → ℤ | v ∈ W ∧ Work.HP.eNorm v ≤ Cp * s 1} : Set (Fin 5 → ℤ)) := by
      rw [hPSetdef]
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_prod]
      tauto
    have hCP0 : (1 : ℝ) ≤ Cp * s 0 := by nlinarith [hs1, hCp1]
    have hCP1 : (1 : ℝ) ≤ Cp * s 1 := by nlinarith [hs1, hs01, hCp1]
    have hA : (({v : Fin 5 → ℤ | v ∈ W ∧ Work.HP.eNorm v ≤ Cp * s 0} :
          Set (Fin 5 → ℤ)).ncard : ℝ) ≤ 8 * C_W * Cp ^ 3 * s 0 ^ 3 := by
      have h1 := hC_W (f44 c) (invSub_finrank_le c hf0 hfirr) (Cp * s 0) hCP0
      have h2 : 1 + Cp * s 0 ≤ 2 * (Cp * s 0) := by linarith
      calc (({v : Fin 5 → ℤ | v ∈ W ∧ Work.HP.eNorm v ≤ Cp * s 0} :
            Set (Fin 5 → ℤ)).ncard : ℝ)
          ≤ C_W * (1 + Cp * s 0) ^ 3 := h1
        _ ≤ C_W * (2 * (Cp * s 0)) ^ 3 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h2 3) hC_Wpos.le
        _ = 8 * C_W * Cp ^ 3 * s 0 ^ 3 := by ring
    have hB : (({v : Fin 5 → ℤ | v ∈ W ∧ Work.HP.eNorm v ≤ Cp * s 1} :
          Set (Fin 5 → ℤ)).ncard : ℝ) ≤ 8 * C_W * Cp ^ 3 * s 1 ^ 3 := by
      have h1 := hC_W (f44 c) (invSub_finrank_le c hf0 hfirr) (Cp * s 1) hCP1
      have h2 : 1 + Cp * s 1 ≤ 2 * (Cp * s 1) := by linarith
      calc (({v : Fin 5 → ℤ | v ∈ W ∧ Work.HP.eNorm v ≤ Cp * s 1} :
            Set (Fin 5 → ℤ)).ncard : ℝ)
          ≤ C_W * (1 + Cp * s 1) ^ 3 := h1
        _ ≤ C_W * (2 * (Cp * s 1)) ^ 3 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h2 3) hC_Wpos.le
        _ = 8 * C_W * Cp ^ 3 * s 1 ^ 3 := by ring
    rw [hprod, Set.ncard_prod, Nat.cast_mul]
    calc (({v : Fin 5 → ℤ | v ∈ W ∧ Work.HP.eNorm v ≤ Cp * s 0} :
            Set (Fin 5 → ℤ)).ncard : ℝ)
          * (({v : Fin 5 → ℤ | v ∈ W ∧ Work.HP.eNorm v ≤ Cp * s 1} :
              Set (Fin 5 → ℤ)).ncard : ℝ)
        ≤ (8 * C_W * Cp ^ 3 * s 0 ^ 3) * (8 * C_W * Cp ^ 3 * s 1 ^ 3) :=
          mul_le_mul hA hB (by positivity) (by positivity)
      _ = 64 * C_W ^ 2 * Cp ^ 6 * s 0 ^ 3 * s 1 ^ 3 := by ring
  -- ### Assembly
  have hunion : (badSet c s).ncard ≤ (badASet c s).ncard + (bad2Set c s).ncard := by
    have h1 : (badSet c s).ncard ≤ (badASet c s ∪ bad2Set c s).ncard :=
      Set.ncard_le_ncard hcover (hBadA_fin.union hBad2_fin)
    calc (badSet c s).ncard ≤ (badASet c s ∪ bad2Set c s).ncard := h1
      _ ≤ (badASet c s).ncard + (bad2Set c s).ncard := Set.ncard_union_le _ _
  have hP1 : (1 : ℝ) ≤ s 0 ^ 3 * s 1 ^ 5 * s 2 ^ 2 := by
    have h0 : (1 : ℝ) ≤ s 0 := hs1
    have h1 : (1 : ℝ) ≤ s 1 := le_trans hs1 hs01
    have h2 : (1 : ℝ) ≤ s 2 := le_trans h1 hs12
    have hp0 : (1 : ℝ) ≤ s 0 ^ 3 := one_le_pow₀ h0
    have hp1 : (1 : ℝ) ≤ s 1 ^ 5 := one_le_pow₀ h1
    have hp2 : (1 : ℝ) ≤ s 2 ^ 2 := one_le_pow₀ h2
    have hp01 : (1 : ℝ) ≤ s 0 ^ 3 * s 1 ^ 5 := by nlinarith [hp0, hp1]
    nlinarith [hp01, hp2]
  have hkey : (64 * C_W ^ 2 * Cp ^ 6 * s 0 ^ 3 * s 1 ^ 3) * (C_F * s 1 ^ 2 * s 2 ^ 2)
      = 64 * C_W ^ 2 * Cp ^ 6 * C_F * (s 0 ^ 3 * s 1 ^ 5 * s 2 ^ 2) := by ring
  calc ((badSet c s).ncard : ℝ)
      ≤ ((badASet c s).ncard : ℝ) + ((bad2Set c s).ncard : ℝ) := by exact_mod_cast hunion
    _ ≤ 1 + (64 * C_W ^ 2 * Cp ^ 6 * s 0 ^ 3 * s 1 ^ 3) * (C_F * s 1 ^ 2 * s 2 ^ 2) := by
        have h1 : ((badASet c s).ncard : ℝ) ≤ 1 := by exact_mod_cast hBadA_le
        have h2 : ((bad2Set c s).ncard : ℝ)
            ≤ (64 * C_W ^ 2 * Cp ^ 6 * s 0 ^ 3 * s 1 ^ 3) * (C_F * s 1 ^ 2 * s 2 ^ 2) :=
          le_trans hBad2_le (mul_le_mul_of_nonneg_right hPSet_le (by positivity))
        linarith
    _ ≤ (64 * C_W ^ 2 * Cp ^ 6 * C_F + 1) * s 0 ^ 3 * s 1 ^ 5 * s 2 ^ 2 := by
        rw [hkey]
        nlinarith [hP1]

end Work.Q44Geom
