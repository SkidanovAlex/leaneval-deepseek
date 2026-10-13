import Mathlib
import Submission.Work.DSM4p.Completion
import Submission.Work.DSM4p.Chart
import Submission.Work.DSM4p.Basic
import Submission.Work.DSM4p.chartComp_isAdicComplete
import Submission.Work.DSM4p.chartComp_modPow

namespace Work.DSM4p

/-
(File `Submission/Work/DSM4p/chartComp_exists_tr.lean`, namespace `Work.DSM4p`.)
There is a tower of transition maps on the completed chart levels, compatible with the
tower of inclusions `Work.DSM4p.chartTr` of the chart levels.

The transition `tr n : chartComp hgr Q (n+1) →ₐ[B] chartComp hgr Q n` is produced, at each
level `n`, from the universal property `AdicCompletion.liftAlgHom` of the `p`-adic completion
`chartComp hgr Q n = AdicCompletion (p) (chartRing hgr Q.ϖ n)`: the compatible family of maps
into the quotients `chartRing hgr Q.ϖ n ⧸ (p)^m` is

  `f m := chartTrQuot m ∘ AdicCompletion.evalₐ (p) m`,

where `chartTrQuot m` is the algebra map on the `p ^ m`-quotients induced by `chartTr n` (it
exists because `chartTr n` sends `p` to `p`).  Compatibility with `chartTr n` is then a
consequence of `AdicCompletion.evalₐ_liftAlgHom`, `AdicCompletion.evalₐ_of` and the defining
property of `chartTrQuot`.
-/

universe a

open DSMap

variable {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B] {gr : ℕ → B}

/-- **The `evalₐ` tower of an adic completion.**  The algebra maps
`AdicCompletion.evalₐ I n : AdicCompletion I R →ₐ[R] R ⧸ I ^ n` form a compatible tower: for
`m ≤ n`, `evalₐ I m` is `evalₐ I n` followed by the projection `R ⧸ I ^ n → R ⧸ I ^ m`.
(This is the `evalₐ`-counterpart of `AdicCompletion.transitionMap_comp_eval`.) -/
theorem AdicCompletion.factor_evalₐ {R : Type*} [CommRing R] (I : Ideal R) {m n : ℕ}
    (hle : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hle) (AdicCompletion.evalₐ I n x)
      = AdicCompletion.evalₐ I m x := by
  induction x using AdicCompletion.induction_on with
  | _ f =>
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    have hmem : (f.val m : R) - f.val n ∈ (I ^ m • ⊤ : Submodule R R) :=
      SModEq.sub_mem.mp (f.property hle)
    have htop : (I ^ m • ⊤ : Submodule R R) = (I ^ m : Ideal R) := by ext y; simp
    rw [htop] at hmem
    simpa only [neg_sub] using neg_mem hmem

/-- `chartTr` sends the natural number `k` (in particular the prime `p`) to itself. -/
theorem chartTr_natCast (hgr : IsRootSystem p gr) (ϖ : ℕ → B) (n : ℕ) (k : ℕ) :
    (chartTr hgr ϖ n).toRingHom (k : chartRing hgr ϖ (n + 1)) = (k : chartRing hgr ϖ n) := by
  simp

/-- The vanishing condition which makes `chartTr n` descend to the `p ^ m`-quotients: the
`p ^ m`-th power ideal is mapped into itself, because `chartTr n` sends `p` to `p`. -/
theorem chartTrQuot_aux (hgr : IsRootSystem p gr) (Q : PerfectoidData p B) (n m : ℕ) :
    ∀ a ∈ (Ideal.span {(p : chartRing hgr Q.ϖ (n + 1))}) ^ m,
      ((Ideal.Quotient.mkₐ B ((Ideal.span {(p : chartRing hgr Q.ϖ n)}) ^ m)).comp
        (chartTr hgr Q.ϖ n)) a = 0 := by
  intro a ha
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  have hle : (Ideal.span {(p : chartRing hgr Q.ϖ (n + 1))}) ^ m ≤
      Ideal.comap (chartTr hgr Q.ϖ n).toRingHom
        ((Ideal.span {(p : chartRing hgr Q.ϖ n)}) ^ m) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
      Ideal.map_span, Set.image_singleton, map_pow, chartTr_natCast]
  exact hle ha

/-- The algebra map on the `p ^ m`-quotients of the chart levels induced by `chartTr n`.  It
exists because `chartTr n` maps `p` to `p`, hence `(p) ^ m` into `(p) ^ m`. -/
noncomputable def chartTrQuot (hgr : IsRootSystem p gr) (Q : PerfectoidData p B) (n m : ℕ) :
    chartRing hgr Q.ϖ (n + 1) ⧸ (Ideal.span {(p : chartRing hgr Q.ϖ (n + 1))}) ^ m →ₐ[B]
      chartRing hgr Q.ϖ n ⧸ (Ideal.span {(p : chartRing hgr Q.ϖ n)}) ^ m :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ B _).comp (chartTr hgr Q.ϖ n))
    (chartTrQuot_aux hgr Q n m)

/-- `chartTrQuot` computes as `chartTr n` on representatives. -/
theorem chartTrQuot_mk (hgr : IsRootSystem p gr) (Q : PerfectoidData p B) (n m : ℕ)
    (y : chartRing hgr Q.ϖ (n + 1)) :
    chartTrQuot hgr Q n m
        (Ideal.Quotient.mk ((Ideal.span {(p : chartRing hgr Q.ϖ (n + 1))}) ^ m) y) =
      Ideal.Quotient.mk ((Ideal.span {(p : chartRing hgr Q.ϖ n)}) ^ m)
        (chartTr hgr Q.ϖ n y) := by
  have h := congr($(Ideal.Quotient.liftₐ_comp ((Ideal.span {(p : chartRing hgr Q.ϖ (n + 1))}) ^ m)
      ((Ideal.Quotient.mkₐ B ((Ideal.span {(p : chartRing hgr Q.ϖ n)}) ^ m)).comp
        (chartTr hgr Q.ϖ n))
      (chartTrQuot_aux hgr Q n m)) y)
  simpa [chartTrQuot, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using h

/-- `chartTrQuot` is compatible with the projections between the `p ^ m`-quotients. -/
theorem chartTrQuot_compat (hgr : IsRootSystem p gr) (Q : PerfectoidData p B) (n : ℕ)
    {m k : ℕ} (hle : m ≤ k)
    (z : chartRing hgr Q.ϖ (n + 1) ⧸ (Ideal.span {(p : chartRing hgr Q.ϖ (n + 1))}) ^ k) :
    (Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right hle)) (chartTrQuot hgr Q n k z) =
      chartTrQuot hgr Q n m
        ((Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right hle)) z) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [chartTrQuot_mk, Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk,
    Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk, chartTrQuot_mk]

/-
(File `Submission/Work/DSM4p/chartComp_exists_tr.lean`, namespace `Work.DSM4p`.)
There is a tower of transition maps on the completed chart levels, compatible with the
tower of inclusions `Work.DSM4p.chartTr` of the chart levels.  Proof plan: for each `n`, apply
`IsAdicComplete.liftAlgHom` (completeness is `Work.DSM4p.chartComp_isAdicComplete`) to the
compatible family `f m : chartComp hgr Q (n+1) →ₐ[B] chartComp hgr Q n ⧸ (span {p})^m` given by
`f m := (quotient iso)⁻¹ ∘ chartTrQuot m ∘ AdicCompletion.evalₐ`, where
`chartTrQuot m : chartRing hgr Q.ϖ (n+1) ⧸ (p)^m →ₐ[B] chartRing hgr Q.ϖ n ⧸ (p)^m` is
induced by `chartTr n`, and where `chartComp hgr Q n ⧸ (span {p})^m ≅ chartRing hgr Q.ϖ n ⧸ (p)^m`
is the image of `AdicCompletion.evalₐ` (whose kernel is `(span {p})^m` by
`Work.DSM4p.ker_evalₐ_eq_pow` + `Ideal.map_span`).  The desired compatibility with `chartTr`
is then checked with `AdicCompletion.ext_evalₐ`/Hausdorffness against `mk_liftAlgHom`.
-/
theorem chartComp_exists_tr {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    {gr : ℕ → B} (hgr : Work.DSM4p.IsRootSystem p gr) (Q : DSMap.PerfectoidData p B) :
    ∃ tr : ∀ n, Work.DSM4p.chartComp hgr Q (n + 1) →ₐ[B] Work.DSM4p.chartComp hgr Q n,
      ∀ (n : ℕ) (y : Work.DSM4p.chartRing hgr Q.ϖ (n + 1)),
        tr n (AdicCompletion.of (Ideal.span {(p : Work.DSM4p.chartRing hgr Q.ϖ (n + 1))})
            (Work.DSM4p.chartRing hgr Q.ϖ (n + 1)) y)
          = AdicCompletion.of (Ideal.span {(p : Work.DSM4p.chartRing hgr Q.ϖ n)})
              (Work.DSM4p.chartRing hgr Q.ϖ n) (Work.DSM4p.chartTr hgr Q.ϖ n y) := by
  classical
  have key : ∀ n, ∃ tr : chartComp hgr Q (n + 1) →ₐ[B] chartComp hgr Q n,
      ∀ y : chartRing hgr Q.ϖ (n + 1),
        tr (AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ (n + 1))})
            (chartRing hgr Q.ϖ (n + 1)) y)
          = AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)})
              (chartRing hgr Q.ϖ n) (chartTr hgr Q.ϖ n y) := by
    intro n
    let f : (m : ℕ) → chartComp hgr Q (n + 1) →ₐ[B]
        chartRing hgr Q.ϖ n ⧸ (Ideal.span {(p : chartRing hgr Q.ϖ n)}) ^ m :=
      fun m => (chartTrQuot hgr Q n m).comp
        ((AdicCompletion.evalₐ (Ideal.span {(p : chartRing hgr Q.ϖ (n + 1))}) m).restrictScalars B)
    have hf : ∀ {m k : ℕ} (hle : m ≤ k),
        (Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right hle)).comp (f k) = f m := by
      intro m k hle
      ext x
      show (Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right hle))
          (chartTrQuot hgr Q n k (AdicCompletion.evalₐ
            (Ideal.span {(p : chartRing hgr Q.ϖ (n + 1))}) k x)) =
          chartTrQuot hgr Q n m (AdicCompletion.evalₐ
            (Ideal.span {(p : chartRing hgr Q.ϖ (n + 1))}) m x)
      have h1 : AdicCompletion.evalₐ (Ideal.span {(p : chartRing hgr Q.ϖ (n + 1))}) m x =
          (Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right hle))
            (AdicCompletion.evalₐ (Ideal.span {(p : chartRing hgr Q.ϖ (n + 1))}) k x) := by
        rw [Ideal.Quotient.factorₐ_apply]
        exact (AdicCompletion.factor_evalₐ _ hle x).symm
      rw [h1, chartTrQuot_compat hgr Q n hle]
    exact ⟨AdicCompletion.liftAlgHom (Ideal.span {(p : chartRing hgr Q.ϖ n)}) f hf,
      fun y => by
        refine AdicCompletion.ext_evalₐ fun m => ?_
        have hL : AdicCompletion.evalₐ (Ideal.span {(p : chartRing hgr Q.ϖ n)}) m
            (AdicCompletion.liftAlgHom (Ideal.span {(p : chartRing hgr Q.ϖ n)}) f hf
              (AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ (n + 1))})
                (chartRing hgr Q.ϖ (n + 1)) y)) =
            Ideal.Quotient.mk ((Ideal.span {(p : chartRing hgr Q.ϖ n)}) ^ m)
              (chartTr hgr Q.ϖ n y) := by
          rw [AdicCompletion.evalₐ_liftAlgHom]
          show chartTrQuot hgr Q n m
              (AdicCompletion.evalₐ (Ideal.span {(p : chartRing hgr Q.ϖ (n + 1))}) m
                (AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ (n + 1))})
                  (chartRing hgr Q.ϖ (n + 1)) y)) = _
          rw [AdicCompletion.evalₐ_of, chartTrQuot_mk]
        have hR : AdicCompletion.evalₐ (Ideal.span {(p : chartRing hgr Q.ϖ n)}) m
            (AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)})
              (chartRing hgr Q.ϖ n) (chartTr hgr Q.ϖ n y)) =
            Ideal.Quotient.mk ((Ideal.span {(p : chartRing hgr Q.ϖ n)}) ^ m)
              (chartTr hgr Q.ϖ n y) :=
          AdicCompletion.evalₐ_of _ m _
        rw [hL, hR]⟩
  choose tr htr using key
  exact ⟨tr, htr⟩

end Work.DSM4p
