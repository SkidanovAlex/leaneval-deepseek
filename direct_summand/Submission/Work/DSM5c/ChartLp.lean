import Submission.Work.DSM5c.ChartFunctor
import Submission.Work.DSPB2.Main

/-!
# DSM5c — the mod-`p` comparison presheaf `Lp` and the termwise surjection `Dp ⟶ Lp`

The M5c transport (design `sources/dsmap/direct_summand_mix2.md` §Task 1 (4), `NOTES.md` §20.2)
goes through the *mod-`p` comparison* of the chart untilts.  This file fixes its vocabulary:

* `Work.DSM5c.pb2Equiv` — **PB2 at the base**: the ring isomorphism `W ⧸ (p) ≃+* W♭ ⧸ (ϖ♭) ^ p` of
  `DSMap.Mix.perfectoid_modp_tilt_proved`, with `Work.DSM5c.pb2Equiv_mk_untilt` as its defining
  property (it inverts the `♯`-map modulo `p`);

* `Work.DSM5c.chartLIdeal`, `Work.DSM5c.chartLAlg` — the ideal `(φ_S (ϖ♭) ^ p) ⊆ R_S` and the
  `W`-algebra structure on the *mod-`p` chart* `L_S := R_S ⧸ (φ_S (ϖ♭) ^ p)`, obtained through
  `W → W ⧸ (p) --pb2Equiv--> W♭ ⧸ (ϖ♭)^p --φ_S--> R_S ⧸ (φ_S (ϖ♭)^p)`.  This is *not* the
  `W`-structure of the quotient induced by the `W♭`-algebra structure of `R_S` (there is no ring map
  `W → W♭`); the point of PB2 is that this quotient is nevertheless a `W`-module.  It is exactly the
  "vector match" of the M5c design: the class of `ϖ_k ∈ W` in `L_S` is the class of the tilt
  `(ϖ♭) ^ (1/p^k)` of `ϖ_k` in `R_S`;

* `Work.DSM5c.chartLMap` — the restriction maps `L_S → L_T` for `S ⊆ T`, induced by `tiltChartRes`
  (`Work.DSM5c.chartLMap_mk`), compatible with the `W`-structures
  (`Work.DSM5c.chartLMap_algebraMap`) and functorial (`chartLMap_self`, `chartLMap_comp`);

* `Work.DSM5c.chartLp` — the presheaf `S ↦ L_S` of `W`-modules;

* `Work.DSM5c.chartLCoaug` — its coaugmentation `W → ∏_i L_{i}`, the comparison-level image of the
  chart coaugmentation `Work.DSM5c.chartCoaugW`.  The M5c transport needs
  `AlmostAcyc Q.ϖ (span {p}) (Č(chartLp)) chartLCoaug`, which is the dévissage-free form of the
  characteristic-`p` input `area_M5b` read through the mod-`p` comparison; that transfer is
  `Submission/Work/DSM5c/LpInput.lean`.

The remaining dictionary:
`Work.DSM5c.chartDToLp` is the termwise surjection `Dp ⟶ Lp` of the transport, with kernel
`(p) · ⊤` (`Work.DSM5c.chartDToLp_ker`), built from
`Work.DSM5c.mem_span_p_sup_map_ker_fontaineTheta` (`D_S ⧸ (p) ≅ L_S`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.DSM5c

universe a

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

section Pb2

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W]

/-- **PB2 at the base** (`DSMap.Mix.perfectoid_modp_tilt_proved`): the mod-`p` tilt identification
`W ⧸ (p) ≃+* W♭ ⧸ (ϖ♭)^p` for the base perfectoid ring `W`, with `ϖ♭ = Work.DSM5c.tiltVarpi Q`.
It is characterized by `Work.DSM5c.pb2Equiv_mk_untilt`: it inverts the `♯`-map modulo `p`. -/
noncomputable def pb2Equiv (Q : PerfectoidData p W) :
    (W ⧸ Ideal.span {(p : W)}) ≃+* (PreTilt W p ⧸ Ideal.span {tiltVarpi Q ^ p}) :=
  (DSMap.Mix.perfectoid_modp_tilt_proved p W Q (tiltVarpi Q)
    (by rw [tiltVarpi_eq_varpiTilt]; exact Work.DSPB1.varpiTilt_untilt Q)).choose

/-- The defining property of `Work.DSM5c.pb2Equiv`: it is inverse to the `♯`-map. -/
theorem pb2Equiv_mk_untilt (Q : PerfectoidData p W) (x : PreTilt W p) :
    pb2Equiv Q (Ideal.Quotient.mk _ (PreTilt.untilt x)) = Ideal.Quotient.mk _ x :=
  (DSMap.Mix.perfectoid_modp_tilt_proved p W Q (tiltVarpi Q)
    (by rw [tiltVarpi_eq_varpiTilt]; exact Work.DSPB1.varpiTilt_untilt Q)).choose_spec x

end Pb2

section Lp

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W]
variable {ι : Type a} [DecidableEq ι]

/-- The ideal `(φ_S (ϖ♭) ^ p) ⊆ R_S` cutting out the mod-`p` chart `L_S := R_S ⧸ (φ_S (ϖ♭) ^ p)`
out of the perfected tilted chart `R_S`. -/
noncomputable def chartLIdeal (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : Finset ι) : Ideal (tiltChart Q t tr htr0 htr j₀ e S) :=
  Ideal.span {chartPhi Q t tr htr0 htr j₀ e S (tiltVarpi Q) ^ p}

@[simp] theorem chartLIdeal_def (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : Finset ι) :
    chartLIdeal Q t tr htr0 htr j₀ e S =
      Ideal.span {chartPhi Q t tr htr0 htr j₀ e S (tiltVarpi Q) ^ p} := rfl

/-- The ring homomorphism `W → L_S` underlying the `W`-algebra structure of the mod-`p` chart:
`W → W ⧸ (p) ≃ W♭ ⧸ (ϖ♭)^p → R_S ⧸ (φ_S (ϖ♭)^p)`. -/
noncomputable def chartLRingHom (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : Finset ι) :
    W →+* (tiltChart Q t tr htr0 htr j₀ e S ⧸ chartLIdeal Q t tr htr0 htr j₀ e S) :=
  (Ideal.Quotient.lift (Ideal.span {tiltVarpi Q ^ p})
    ((Ideal.Quotient.mk (chartLIdeal Q t tr htr0 htr j₀ e S)).comp
      (chartPhi Q t tr htr0 htr j₀ e S))
    (fun x hx => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [RingHom.comp_apply, map_mul, map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))).comp
    ((pb2Equiv (p := p) (W := W) Q).toRingHom.comp
      (Ideal.Quotient.mk (Ideal.span {(p : W)})))

/-- **The `W`-algebra structure of the mod-`p` chart** `L_S = R_S ⧸ (φ_S (ϖ♭) ^ p)`, through PB2:
`W → W ⧸ (p) ≃ W♭ ⧸ (ϖ♭)^p → R_S ⧸ (φ_S (ϖ♭)^p)`. -/
noncomputable def chartLAlg (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : Finset ι) :
    Algebra W (tiltChart Q t tr htr0 htr j₀ e S ⧸ chartLIdeal Q t tr htr0 htr j₀ e S) :=
  letI : SMul W (tiltChart Q t tr htr0 htr j₀ e S ⧸ chartLIdeal Q t tr htr0 htr j₀ e S) :=
    ⟨fun w x => chartLRingHom Q t tr htr0 htr j₀ e S w * x⟩
  Algebra.mk (chartLRingHom Q t tr htr0 htr j₀ e S)
    (fun r x => mul_comm (chartLRingHom Q t tr htr0 htr j₀ e S r) x)
    (fun r x => rfl)

/-- **The restriction map of the mod-`p` charts**: `L_S → L_T` for `S ⊆ T`, induced by the tilted
chart restriction `tiltChartRes`. -/
noncomputable def chartLMap (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    {S T : Finset ι} (h : S ⊆ T) :
    (tiltChart Q t tr htr0 htr j₀ e S ⧸ chartLIdeal Q t tr htr0 htr j₀ e S) →+*
      (tiltChart Q t tr htr0 htr j₀ e T ⧸ chartLIdeal Q t tr htr0 htr j₀ e T) :=
  Ideal.Quotient.lift (chartLIdeal Q t tr htr0 htr j₀ e S)
    ((Ideal.Quotient.mk (chartLIdeal Q t tr htr0 htr j₀ e T)).comp
      (tiltChartRes Q t tr htr0 htr j₀ e h))
    (fun x hx => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      have hφ : tiltChartRes Q t tr htr0 htr j₀ e h
          ((chartPhi Q t tr htr0 htr j₀ e S) (tiltVarpi Q)) =
          (chartPhi Q t tr htr0 htr j₀ e T) (tiltVarpi Q) :=
        tiltChartRes_algebraMap Q t tr htr0 htr j₀ e h (tiltVarpi Q)
      show Ideal.Quotient.mk (chartLIdeal Q t tr htr0 htr j₀ e T)
        (tiltChartRes Q t tr htr0 htr j₀ e h
          (c * (chartPhi Q t tr htr0 htr j₀ e S) (tiltVarpi Q) ^ p)) = 0
      rw [map_mul, map_pow, hφ, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self
        ((chartPhi Q t tr htr0 htr j₀ e T) (tiltVarpi Q) ^ p)))

/-- The defining property of `chartLMap` on classes. -/
theorem chartLMap_mk (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    {S T : Finset ι} (h : S ⊆ T) (x : tiltChart Q t tr htr0 htr j₀ e S) :
    chartLMap Q t tr htr0 htr j₀ e h (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (tiltChartRes Q t tr htr0 htr j₀ e h x) :=
  Ideal.Quotient.lift_mk _ _ _

/-- The self-map of the mod-`p` chart is the identity on classes. -/
theorem chartLMap_self_mk (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : Finset ι) (x : tiltChart Q t tr htr0 htr j₀ e S) :
    chartLMap Q t tr htr0 htr j₀ e (subset_refl S) (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ x := by
  rw [chartLMap_mk]
  rw [show tiltChartRes Q t tr htr0 htr j₀ e (subset_refl S) x = x from by
    rw [tiltChartRes_self]; rfl]

/-- The composition rule for the mod-`p` chart restrictions, on classes. -/
theorem chartLMap_comp_mk (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    {S T V : Finset ι} (h₁ : S ⊆ T) (h₂ : T ⊆ V) (x : tiltChart Q t tr htr0 htr j₀ e S) :
    chartLMap Q t tr htr0 htr j₀ e (h₁.trans h₂) (Ideal.Quotient.mk _ x) =
      chartLMap Q t tr htr0 htr j₀ e h₂
        (chartLMap Q t tr htr0 htr j₀ e h₁ (Ideal.Quotient.mk _ x)) := by
  rw [chartLMap_mk, chartLMap_mk, chartLMap_mk]
  have hcomp : tiltChartRes Q t tr htr0 htr j₀ e (h₁.trans h₂) x =
      tiltChartRes Q t tr htr0 htr j₀ e h₂
        (tiltChartRes Q t tr htr0 htr j₀ e h₁ x) := by
    have h := congrArg (fun (f : tiltChart Q t tr htr0 htr j₀ e S →+*
        tiltChart Q t tr htr0 htr j₀ e V) => f x)
      (tiltChartRes_comp Q t tr htr0 htr j₀ e h₁ h₂)
    simpa using h.symm
  rw [hcomp]

end Lp

end Work.DSM5c
