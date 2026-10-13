-- NOTE (WilC5 / S4OnePoint_general): a clash-free *copy* of `Submission/Work/WilC5/StepNoNewLog.lean`:
-- the import of the `StepNoNewPrep`/`StepNoNew` chain is redirected to the corresponding
-- `…Cut` copies, in which the auxiliary definition `mkSubAt` is renamed to `mkSubAtSN`, because
-- the original `Work.WilC5.mkSubAt` clashes with the identically named definition of
-- `Submission/Work/WilC5/S4ExpG/Glue.lean` (which the §4 Lemma-4.4 assembly needs through
-- `ExistsStepSeq`/`StepSeqDecomp`/`DclExtensionCast`).

/-
  WilC5 — the **log half of vdDMM Lemma 4.2**: the domain `F = Dcl (B ∪ {x})` of the "no new
  value" step is closed under the definable logarithm, and the partial embedding `g` (an
  `LRc`-embedding of `K` into `L` extending the map on `B`) commutes with it on `F`.

  The value-theoretic input is the hypothesis `hvg`: every element of `F = Dcl (B ∪ {x})` has the
  value of an element of `B` (`v(F^×) = v(B^×)`).  For `0 < w ∈ F` this gives `b ∈ B` with
  `v(w) = v(b)`, so `w = (c_r b)(1 + ε)` with `c_r b ∈ B` and `ε` infinitesimal
  (`decomposition_of_same_value`, the residue field of a model of `TR` being `ℝ`); then

    `log w = log (c_r b) + log (1 + ε)`,

  where `log (c_r b) ∈ B` and — for `|2ε| ≤ 1`, which holds because `ε` is infinitesimal — the
  element `log (1+ε)` is *the unique* `u` with `rexp u = 1 + ε` (`logFun_one_add_rexp`,
  `logFun_eq_of_rexp_eq`).  Since that condition is `LRc`-definable with the parameters `w`, `c_r b`
  in `F`, it gives `log (1+ε) ∈ F` (`mem_dcl_of_unique_solution`), hence `F` is log-closed; and the
  same identity on the `L`-side, together with the fact that `g` commutes with the `rexp` symbol,
  gives `g (log w) = log (g w)`.

  Everything is carried out at the `rexp`-reduct `Work.WilC5.reductStruct`; the only use of the
  canonical structure is the `[K ⊨ TR]` instance demanded by `decomposition_of_same_value`.
-/
import Mathlib
import Submission.Work.WilC5.StepNoNewPrepCut

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

theorem logHalf {K L : Type} [LEc.Structure K] [LEc.Structure L]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Ring.CompatibleRing K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [Ring.CompatibleRing L]
    (hK : K ⊨ TE) (hL : L ⊨ TE)
    (hKTRcan : @Theory.Model LRc K (canonStruct K) TR)
    (hstructK : (reductStruct K : LRc.Structure K) = canonStruct K)
    (hleEK : ∀ u v : K, leE u v ↔ u ≤ v)
    (haddK : ∀ u v : K, addE u v = u + v) (hmulK : ∀ u v : K, mulE u v = u * v)
    (honeK : (oneE : K) = 1) (hzeroK : (zeroE : K) = 0) (hnegK : ∀ u : K, negE u = -u)
    (hleEL : ∀ u v : L, leE u v ↔ u ≤ v) (hzeroL : (zeroE : L) = 0)
    (B : Set K) (S : @LRc.Substructure K (reductStruct K)) (x : K)
    (hScoe : (S : Set K) = @Work.WilC2.Dcl K (reductStruct K) (B ∪ {x}))
    (hdclidem : @Work.WilC2.Dcl K (reductStruct K) (@Work.WilC2.Dcl K (reductStruct K) (B ∪ {x}))
      = @Work.WilC2.Dcl K (reductStruct K) (B ∪ {x}))
    (hBsub : B ⊆ (S : Set K))
    (hBlog : ∀ b ∈ B, logFun b ∈ B)
    (hBconst : ∀ r : ℝ, realConst K r ∈ B)
    (hBmul : ∀ u ∈ B, ∀ v ∈ B, mulE u v ∈ B) (hBzero : (0 : K) ∈ B)
    (g : @Embedding LRc K L (reductStruct K) (reductStruct L))
    (hglog : ∀ b ∈ B, g (logFun b) = logFun (g b))
    (hvg : ∀ w : K, w ∈ @Work.WilC2.Dcl K (reductStruct K) (B ∪ {x}) →
      ∃ b ∈ B, SameArch w b) :
    LogClosed (S : Set K) ∧ (∀ w : K, w ∈ (S : Set K) → g (logFun w) = logFun (g w)) := by
  letI : LRc.Structure K := reductStruct K
  letI : LRc.Structure L := reductStruct L
  haveI := hKTRcan
  -- `Dcl` computed at the canonical structure is `Dcl` computed at the reduct
  have htransK : @Work.WilC2.Dcl K (canonStruct K) (B ∪ {x})
      = @Work.WilC2.Dcl K (reductStruct K) (B ∪ {x}) :=
    congrArg (fun i => @Work.WilC2.Dcl K i (B ∪ {x})) hstructK.symm
  -- ------------------------------------------------------------------ #
  -- bridges between the `LRc`- and the `LEc`-form of the ring operations
  -- ------------------------------------------------------------------ #
  have hmulEL2 : ∀ u v : K, @mulEL K (reductStruct K) u v = mulE u v := by
    intro u v
    show @Structure.funMap LRc K (reductStruct K) 2 (Sum.inl (Sum.inl Ring.mulFunc)) ![u, v]
      = @Structure.funMap LEc K _ 2 (ringSym Ring.mulFunc) ![u, v]
    rw [reductStruct_funMap_ring]
  have haddEL2 : ∀ u v : K, @addEL K (reductStruct K) u v = addE u v := by
    intro u v
    show @Structure.funMap LRc K (reductStruct K) 2 (Sum.inl (Sum.inl Ring.addFunc)) ![u, v]
      = @Structure.funMap LEc K _ 2 (ringSym Ring.addFunc) ![u, v]
    rw [reductStruct_funMap_ring]
  have honeEL2 : (@oneEL K (reductStruct K)) = oneE := by
    show @Structure.funMap LRc K (reductStruct K) 0 (Sum.inl (Sum.inl Ring.oneFunc)) default
      = @Structure.funMap LEc K _ 0 (ringSym Ring.oneFunc) default
    rw [reductStruct_funMap_ring]
  -- `S` is closed under addition (the `LRc` addition is `addE`)
  have hAddMem : ∀ a b : K, a ∈ (S : Set K) → b ∈ (S : Set K) → addE a b ∈ (S : Set K) := by
    intro a b ha hb
    have h := S.fun_mem (ringSymL Ring.addFunc) ![a, b]
      (by intro i; fin_cases i <;> assumption)
    have h' : @addEL K (reductStruct K) a b ∈ (S : Set K) := h
    rwa [haddEL2] at h'
  -- positivity in the `leE`-form is positivity for the order
  have hposK : ∀ {y : K}, leE zeroE y → ¬ leE y zeroE → (0 : K) < y := by
    intro y h1 h2
    have h1' : (0 : K) ≤ y := by rw [← hzeroK]; exact (hleEK zeroE y).mp h1
    have h2' : ¬ y ≤ (0 : K) := by rw [← hzeroK]; exact fun hy => h2 ((hleEK y zeroE).mpr hy)
    exact lt_of_le_not_ge h1' h2'
  have hposL : ∀ {y : L}, leE zeroE y → ¬ leE y zeroE → (0 : L) < y := by
    intro y h1 h2
    have h1' : (0 : L) ≤ y := by rw [← hzeroL]; exact (hleEL zeroE y).mp h1
    have h2' : ¬ y ≤ (0 : L) := by rw [← hzeroL]; exact fun hy => h2 ((hleEL y zeroE).mpr hy)
    exact lt_of_le_not_ge h1' h2'
  -- ------------------------------------------------------------------ #
  -- the value-theoretic extraction
  -- ------------------------------------------------------------------ #
  have hsetup : ∀ (w : K), w ∈ @Work.WilC2.Dcl K (reductStruct K) (B ∪ {x}) → (0 : K) < w →
      ∃ (ρ ε : K) (r : ℝ), ρ ∈ B ∧ (leE zeroE ρ ∧ ¬ leE ρ zeroE) ∧
        (leE zeroE (addE oneE ε) ∧ ¬ leE (addE oneE ε) zeroE) ∧
        ε ∈ (S : Set K) ∧ logFun (addE oneE ε) ∈ (S : Set K) ∧
        absLeOne (mulE (addE oneE oneE) ε) ∧
        w = mulE ρ (addE oneE ε) ∧
        logFun w = addE (logFun ρ) (logFun (addE oneE ε)) := by
    intro w hwD hpos
    obtain ⟨b, hbB, hbs⟩ := hvg w hwD
    have hbne : b ≠ 0 := by
      intro h0
      have h2 : SameArch w (0 : K) := by rw [← h0]; exact hbs
      have h3 : w = 0 := sameArch_eq_zero_right h2
      rw [h3] at hpos
      exact absurd hpos (lt_irrefl 0)
    obtain ⟨r, hrne, ε, hεinf, hdec⟩ := decomposition_of_same_value hbne hbs
    set ρ : K := realConst K r * b with hρdef
    have hεhalf : |ε| ≤ (2 : K)⁻¹ := by
      have h := hεinf 1
      have h2 : (((1 : ℕ) : K) + 1)⁻¹ = (2 : K)⁻¹ := by norm_num
      rwa [h2] at h
    have h1ε : (0 : K) < 1 + ε := by
      have h := abs_le.mp hεhalf
      have h2inv : (0 : K) < (2 : K)⁻¹ := by positivity
      linarith [h.1, h.2, h2inv]
    have hρpos : (0 : K) < ρ := by
      by_contra hcon
      push_neg at hcon
      have hle : ρ * (1 + ε) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon (le_of_lt h1ε)
      have hpos' : (0 : K) < ρ * (1 + ε) := hdec ▸ hpos
      linarith
    have hρB : ρ ∈ B := by
      rw [hρdef, ← hmulK]
      exact hBmul (realConst K r) (hBconst r) b hbB
    have hdec2 : w = mulE ρ (addE oneE ε) := by
      rw [hmulK, haddK, honeK]
      exact hdec
    have hρE : leE zeroE ρ ∧ ¬ leE ρ zeroE := by
      constructor
      · rw [hleEK, hzeroK]; exact le_of_lt hρpos
      · rw [hleEK, hzeroK]; exact not_le.mpr hρpos
    have h1εE : leE zeroE (addE oneE ε) ∧ ¬ leE (addE oneE ε) zeroE := by
      constructor
      · rw [hleEK, hzeroK, haddK, honeK]; exact le_of_lt h1ε
      · rw [hleEK, hzeroK, haddK, honeK]; exact not_le.mpr h1ε
    have habsLe : absLeOne (mulE (addE oneE oneE) ε) := by
      have h2ε : mulE (addE oneE oneE) ε = (2 : K) * ε := by
        rw [hmulK, haddK, honeK]; norm_num
      refine (absLeOne_iff_le haddK hmulK honeK hzeroK hnegK hleEK
        (mulE (addE oneE oneE) ε)).mpr ?_
      rw [h2ε, abs_mul, abs_of_pos (by norm_num : (0 : K) < 2)]
      calc 2 * |ε| ≤ 2 * (2 : K)⁻¹ := mul_le_mul_of_nonneg_left hεhalf (by norm_num)
        _ = 1 := by rw [mul_inv_cancel₀ (by norm_num : (2 : K) ≠ 0)]
    -- `ε ∈ Dcl (B ∪ {x})`: it is the unique `δ` with `w = ρ (1 + δ)`
    have hεD : ε ∈ @Work.WilC2.Dcl K (reductStruct K) (B ∪ {x}) := by
      refine mem_dcl_of_unique_solution (reductStruct K) ![w, ρ] ?_ eqMulForm (u := ε) ?_ ?_
        hdclidem
      · intro j
        fin_cases j
        · exact hwD
        · have h1 : ρ ∈ @Work.WilC2.Dcl K (canonStruct K) (B ∪ {x}) :=
            Work.WilC2.subset_dcl_aux (B ∪ {x}) (Or.inl hρB)
          rwa [htransK] at h1
      · rw [formulaRealize_iff_bounded, eqMulForm_realize]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [hmulEL2, haddEL2, honeEL2]
        exact hdec2
      · intro v hv
        rw [formulaRealize_iff_bounded, eqMulForm_realize] at hv
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv
        rw [hmulEL2, haddEL2, honeEL2] at hv
        have h5 : mulE ρ (addE oneE (v 0)) = mulE ρ (addE oneE ε) := by rw [← hv, hdec2]
        have h3 : ρ * (1 + v 0) = ρ * (1 + ε) := by
          simpa only [hmulK, haddK, honeK] using h5
        have h4 : (1 : K) + v 0 = 1 + ε := mul_left_cancel₀ (ne_of_gt hρpos) h3
        funext j
        rw [Subsingleton.elim j 0]
        linarith
    -- `log (1 + ε) ∈ Dcl (B ∪ {x})`: it is the unique `u` with `rexp u = 1 + ε`
    have hlogεD : logFun (addE oneE ε) ∈ @Work.WilC2.Dcl K (reductStruct K) (B ∪ {x}) := by
      refine mem_dcl_of_unique_solution (reductStruct K) ![ε] ?_ rexpOneAddForm
        (u := logFun (addE oneE ε)) ?_ ?_ hdclidem
      · intro j; fin_cases j; simpa using hεD
      · rw [formulaRealize_iff_bounded, rexpOneAddForm_realize]
        simp only [Matrix.cons_val_zero]
        rw [reductStruct_funMap_rexpSymL, haddEL2, honeEL2]
        exact logFun_one_add_rexp hK habsLe
      · intro v hv
        rw [formulaRealize_iff_bounded, rexpOneAddForm_realize] at hv
        simp only [Matrix.cons_val_zero] at hv
        rw [reductStruct_funMap_rexpSymL, haddEL2, honeEL2] at hv
        funext j
        rw [Subsingleton.elim j 0]
        exact logFun_eq_of_rexp_eq hK habsLe hv
    have hεS : ε ∈ (S : Set K) := by rw [hScoe]; exact hεD
    have hlogεS : logFun (addE oneE ε) ∈ (S : Set K) := by rw [hScoe]; exact hlogεD
    have hlogw : logFun w = addE (logFun ρ) (logFun (addE oneE ε)) := by
      rw [hdec2]
      exact logFun_mul hK hρE h1εE
    exact ⟨ρ, ε, r, hρB, hρE, h1εE, hεS, hlogεS, habsLe, hdec2, hlogw⟩
  -- ------------------------------------------------------------------ #
  -- `F` is closed under the definable logarithm
  -- ------------------------------------------------------------------ #
  have hlogclosed : LogClosed (S : Set K) := by
    intro w hw
    have hwD : w ∈ @Work.WilC2.Dcl K (reductStruct K) (B ∪ {x}) := by rw [← hScoe]; exact hw
    by_cases hpos : (0 : K) < w
    · obtain ⟨ρ, ε, r, hρB, hρE, h1εE, hεS, hlogεS, habsLe, hdec2, hlogw⟩ := hsetup w hwD hpos
      rw [hlogw]
      exact hAddMem (logFun ρ) (logFun (addE oneE ε)) (hBsub (hBlog ρ hρB)) hlogεS
    · have hz : logFun w = (0 : K) := by
        rw [logFun_eq_zero_of_not_pos hK (by
          intro hcon
          exact hpos (hposK hcon.1 hcon.2)), hzeroK]
      rw [hz]
      exact hBsub hBzero
  -- ------------------------------------------------------------------ #
  -- the log-preservation of the extension
  -- ------------------------------------------------------------------ #
  have hlogpres : ∀ w : K, w ∈ (S : Set K) → g (logFun w) = logFun (g w) := by
    intro w hw
    by_cases hpos : (0 : K) < w
    · obtain ⟨ρ, ε, r, hρB, hρE, h1εE, hεS, hlogεS, habsLe, hdec2, hlogw⟩ :=
        hsetup w (by rw [← hScoe]; exact hw) hpos
      -- positivity on the `L`-side, by the order-preservation of `g`
      have hposE' : leE (zeroE : K) w ∧ ¬ leE w (zeroE : K) := by
        constructor
        · rw [hleEK, hzeroK]; exact le_of_lt hpos
        · rw [hleEK, hzeroK]; exact not_le.mpr hpos
      have hposg : (0 : L) < g w := by
        have h := (pos_map_iff_reduct hK hL g w).mp hposE'
        exact hposL h.1 h.2
      have hgρE : leE (zeroE : L) (g ρ) ∧ ¬ leE (g ρ) (zeroE : L) :=
        (pos_map_iff_reduct hK hL g ρ).mp hρE
      have h1gεE : leE (zeroE : L) (addE oneE (g ε)) ∧ ¬ leE (addE oneE (g ε)) (zeroE : L) := by
        have h := (pos_map_iff_reduct hK hL g (addE oneE ε)).mp h1εE
        rwa [map_addE_reduct, map_oneE_reduct] at h
      -- `|2·(g ε)| ≤ 1` on the `L`-side
      have habsLeL : absLeOne (mulE (addE oneE oneE) (g ε)) := by
        have h := map_absLeOne_reduct g habsLe
        rwa [map_mulE_reduct, map_addE_reduct, map_oneE_reduct] at h
      -- the "near `1`" step
      have hnear : g (logFun (addE oneE ε)) = logFun (addE oneE (g ε)) := by
        have hrexpK : @Structure.funMap LRc K (reductStruct K) 1 rexpSymL
            (fun _ : Fin 1 => logFun (addE oneE ε)) = addE oneE ε := by
          rw [reductStruct_funMap_rexpSymL]
          exact logFun_one_add_rexp hK habsLe
        have h1 : g (@Structure.funMap LRc K (reductStruct K) 1 rexpSymL
              (fun _ : Fin 1 => logFun (addE oneE ε)))
            = @Structure.funMap LRc L (reductStruct L) 1 rexpSymL
              (fun _ : Fin 1 => g (logFun (addE oneE ε))) := by
          rw [g.map_fun rexpSymL (fun _ : Fin 1 => logFun (addE oneE ε))]
          congr 1
        rw [hrexpK] at h1
        have h2 : g (addE oneE ε) = addE oneE (g ε) := by
          rw [map_addE_reduct, map_oneE_reduct]
        rw [h2, reductStruct_funMap_rexpSymL] at h1
        exact logFun_eq_of_rexp_eq hL habsLeL h1.symm
      have hBpres : g (logFun ρ) = logFun (g ρ) := hglog ρ hρB
      have hgw : g w = mulE (g ρ) (addE oneE (g ε)) := by
        rw [hdec2, map_mulE_reduct, map_addE_reduct, map_oneE_reduct]
      have hloggw : logFun (g w) = addE (logFun (g ρ)) (logFun (addE oneE (g ε))) := by
        rw [hgw]
        exact logFun_mul hL hgρE h1gεE
      rw [hlogw, map_addE_reduct, hnear, hBpres, ← hloggw]
    · have hz : logFun w = (zeroE : K) := logFun_eq_zero_of_not_pos hK (by
        intro hcon
        exact hpos (hposK hcon.1 hcon.2))
      have hLz : logFun (g w) = (zeroE : L) := logFun_eq_zero_of_not_pos hL (by
        intro hcon
        have h' : leE (zeroE : K) w ∧ ¬ leE w (zeroE : K) :=
          (pos_map_iff_reduct hK hL g w).mpr hcon
        exact hpos (hposK h'.1 h'.2))
      rw [hz, hLz, map_zeroE_reduct]
  exact ⟨hlogclosed, hlogpres⟩

end Work.WilC5
