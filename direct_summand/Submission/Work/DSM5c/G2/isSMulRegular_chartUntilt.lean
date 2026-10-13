import Mathlib
import Submission.Work.DSM5c.ChartFunctor
import Submission.Work.DSM5c.ChartComparison
import Submission.Work.DSM5c.Charts.perfChartRing_perfect
import Submission.Work.DSM5c.Regularity.tiltVarpi_isSMulRegular
import Submission.Work.DSM5c.G2.quotTeichmullerSubPz_torsionFree
import Submission.Work.DSM5c.G2.kerTheta_decomp

/-!
# Gap G2 of the M5c node: `p`-torsion-freeness of the chart untilts `D_S`

This file proves `Work.DSM5c.G2.isSMulRegular_chartUntilt`: the chart untilt

  `D_S = Work.DSM5c.untiltOf R_S φ_S = 𝕎 R_S ⧸ 𝕎(φ_S)(ker θ_W)`,   `R_S = Work.DSM5c.tiltChart … S`,

is `p`-torsion-free.  This is the hypothesis `hreg` of the dévissage `Work.DSM5c.almostAcyc_span_pow`.

## The mathematics

Write `W♭ = PreTilt W p`, `ϖ♭ = Work.DSM5c.tiltVarpi Q`, `𝕎 = WittVector p (PreTilt W p)`,
`θ = WittVector.fontaineTheta W p`.  Let `v : Wˣ` with `Q.ϖ 0 ^ p = p·v` (`Q.unit`) and pick a lift
`z₀` of `v` (`θ z₀ = v`, available since `θ` is onto, see
`surjective_fontaineTheta_of_perfectoidData`).  Put

  `ξ := [ϖ♭ ^ p] - p·z₀ ∈ ker θ`  (`θ ξ = ♯(ϖ♭)^p - p·v = (Q.ϖ 0)^p - p·v = 0`).

For a `W♭`-algebra `φ : W♭ →+* R` with `R` perfect of characteristic `p`, let
`I := 𝕎R·𝕎(φ)(ker θ)` (so `untiltOf R φ = 𝕎R ⧸ I`) and `ξ' := 𝕎φ(ξ) = [φ(ϖ♭)^p] - p·𝕎φ(z₀)`.

There are two ingredients.

* **`I = (ξ') + p·I`** (`span_map_ker_fontaineTheta_eq_xiR_add_mul`).  Every `k ∈ ker θ` decomposes
  as `k = [b]·ξ + p·u` with `u ∈ ker θ` (the delegated `Work.DSM5c.G2.kerTheta_decomp`; this is the
  only place where the mod-`p` comparison `Work.DSM5c.mem_span_p_sup_ker_fontaineTheta`, i.e. `PB2`,
  and the fact that `p` is a non-zero-divisor of `W`, are used).  Applying `𝕎φ` gives
  `𝕎φ(k) = [φ b]·ξ' + p·𝕎φ(u) ∈ (ξ') + p·I`; the reverse inclusion is immediate since `ξ ∈ ker θ`
  and `p·I ⊆ I`.

* **`(ξ' : p) = (ξ')`**, i.e. `𝕎R ⧸ (ξ')` is `p`-torsion-free
  (`Work.DSM5c.G2.quotTeichmullerSubPz_torsionFree`): for `p·y = ξ'·a` one has
  `[c]·a = ξ'·a + p·z·a = p·(y + z·a) ∈ (p)` where `c := φ(ϖ♭)^p`; `constantCoeff` gives
  `c·cc(a) = 0`, so `cc(a) = 0` (regularity of `c`) and `a ∈ (p) = ker constantCoeff`; write
  `a = p·c'`, then `p·y = p·(ξ'·c')` and `p`-torsion-freeness of `𝕎R` gives `y = ξ'·c'`.

Combining: if `p·y ∈ I`, write `p·y = a + p·i₁` with `a ∈ (ξ')` and `i₁ ∈ I` (using `I = (ξ')+p·I`);
then `p·(y - i₁) = a ∈ (ξ')`, so `y - i₁ ∈ (ξ') ⊆ I` and `y ∈ I`.  Hence `(I : p) = I`, i.e. `p` is a
non-zero-divisor of `D_S = 𝕎R ⧸ I`.

For the chart `R = R_S = Work.DSM5c.tiltChart … S` the hypothesis `hc` of
`isSMulRegular_untiltOf_of_regular` is supplied as follows:
* `(p : R_S) = 0`, because `p = 0` in `W♭ = PreTilt W p` and `R_S` is a `W♭`-subalgebra
  (`chart_p_eq_zero`);
* `φ_S(ϖ♭)` is a non-zero-divisor of `R_S`: `ϖ♭` is a non-zero-divisor of `W♭`
  (`Work.DSM5c.Regularity.tiltVarpi_isSMulRegular`), hence so is its image in the localisation
  `(W♭)_{u_S}` (`IsSMulRegular.of_isLocalization`), hence so is the image in the subalgebra
  `R_S ⊆ (W♭)_{u_S}` (`isSMulRegular_subalgebra_algebraMap`);
* `R_S` is perfect (`Work.DSM5c.Charts.perfChartRing_perfect`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.DSM5c.G2

universe u

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

variable {p : ℕ} [Fact p.Prime] {W : Type} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W]

open WittVector

/-! ## The element `ξ` and its image `ξ'` -/

/-- The element `ξ = [ϖ♭ ^ p] - p·z₀ ∈ 𝕎 W♭` of the untilt construction, where
`ϖ♭ = Work.DSM5c.tiltVarpi Q`.  It lies in `ker θ_W` as soon as `θ z₀ = v` with
`Q.ϖ 0 ^ p = p·v` (`fontaineTheta_xiChart`), and its `0`-th coefficient is `ϖ♭ ^ p`. -/
noncomputable def xiChart (Q : PerfectoidData p W) (z₀ : WittVector p (PreTilt W p)) :
    WittVector p (PreTilt W p) :=
  WittVector.teichmuller p (tiltVarpi Q ^ p) - (p : WittVector p (PreTilt W p)) * z₀

/-- The image `ξ' = 𝕎(φ)(ξ) = [φ(ϖ♭) ^ p] - p·𝕎(φ)(z₀)` of `ξ` in `𝕎 R`; this is the element whose
principal ideal occurs in the identity `I = (ξ') + p·I`. -/
noncomputable def xiR (Q : PerfectoidData p W) {R : Type} [CommRing R] (φ : PreTilt W p →+* R)
    (z₀ : WittVector p (PreTilt W p)) : WittVector p R :=
  WittVector.teichmuller p (φ (tiltVarpi Q) ^ p) - (p : WittVector p R) * WittVector.map φ z₀

/-- **The ideal defining the untilt**, `I = 𝕎R·𝕎(φ)(ker θ_W)`; `untiltOf R φ = 𝕎R ⧸ kerIdeal φ`. -/
noncomputable def kerIdeal {R : Type} [CommRing R] (φ : PreTilt W p →+* R) :
    Ideal (WittVector p R) :=
  Ideal.span ((WittVector.map φ) ''
    ((RingHom.ker (WittVector.fontaineTheta (p := p) (R := W)) :
      Set (WittVector p (PreTilt W p)))))

/-- `𝕎(φ)` of `ξ` is `ξ'`. -/
theorem map_xiChart (Q : PerfectoidData p W) {R : Type} [CommRing R] (φ : PreTilt W p →+* R)
    (z₀ : WittVector p (PreTilt W p)) :
    WittVector.map φ (xiChart Q z₀) = xiR Q φ z₀ := by
  rw [xiChart, xiR, map_sub, map_mul, map_natCast, WittVector.map_teichmuller, map_pow]

/-- **`θ` is onto** for an integral perfectoid ring (`Q : PerfectoidData p W`): Frobenius is
surjective on `W ⧸ (p)` (`Q.frobSurj`), and `WittVector.surjective_fontaineTheta` upgrades this to
surjectivity of `θ`. -/
theorem surjective_fontaineTheta_of_perfectoidData (Q : PerfectoidData p W) :
    Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)) := by
  refine surjective_fontaineTheta ?_
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨z, hz⟩ := Q.frobSurj x
  exact ⟨Ideal.Quotient.mk (Ideal.span {(p : W)}) z, by
    rw [frobenius_def, ← map_pow, Ideal.Quotient.eq]
    simpa [sub_eq_add_neg, add_comm] using neg_mem hz⟩

/-- **`ξ ∈ ker θ_W`**: its `θ`-image is `♯(ϖ♭)^p - p·v = (Q.ϖ 0)^p - p·v = 0`. -/
theorem fontaineTheta_xiChart (Q : PerfectoidData p W) (v : Wˣ)
    (hv : Q.ϖ 0 ^ p = (p : W) * (v : W))
    (z₀ : WittVector p (PreTilt W p))
    (hz₀ : WittVector.fontaineTheta (p := p) (R := W) z₀ = (v : W)) :
    WittVector.fontaineTheta (p := p) (R := W) (xiChart Q z₀) = 0 := by
  have htel : WittVector.fontaineTheta (p := p) (R := W)
      (WittVector.teichmuller p (tiltVarpi Q ^ p)) = (Q.ϖ 0) ^ p := by
    rw [WittVector.fontaineTheta_teichmuller, map_pow,
      show PreTilt.untilt (p := p) (O := W) (tiltVarpi Q) = Q.ϖ 0 from by
        rw [tiltVarpi_eq_varpiTilt]
        exact Work.DSPB1.varpiTilt_untilt Q]
  rw [xiChart, map_sub, map_mul, map_natCast, htel, hz₀, hv]
  ring

/-! ## Two elementary transport lemmas -/

/-- **`p`-torsion-freeness passes to quotients.**  If `r·y ∈ I` implies `y ∈ I`, then `r` is a
non-zero-divisor on the quotient `A ⧸ I`. -/
theorem isSMulRegular_quotient_of_mul_mem {A : Type u} [CommRing A] (I : Ideal A) (r : A)
    (h : ∀ y : A, r * y ∈ I → y ∈ I) :
    IsSMulRegular (A ⧸ I) (Ideal.Quotient.mk I r) := by
  rw [IsSMulRegular]
  intro y z hyz
  obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨z', rfl⟩ := Ideal.Quotient.mk_surjective z
  have h1 : (Ideal.Quotient.mk I r) * (Ideal.Quotient.mk I y') =
      (Ideal.Quotient.mk I r) * (Ideal.Quotient.mk I z') := by
    simpa [smul_eq_mul] using hyz
  rw [← map_mul, ← map_mul] at h1
  have hmem : r * (y' - z') ∈ I := by
    have h2 : r * y' - r * z' ∈ I := Ideal.Quotient.eq.mp h1
    simpa [mul_sub] using h2
  rw [Ideal.Quotient.eq]
  exact h (y' - z') hmem

/-- **Regularity passes to subalgebras**: if `algebraMap R A x` is a non-zero-divisor of `A`, so is
its image in an `R`-subalgebra `S ⊆ A`. -/
theorem isSMulRegular_subalgebra_algebraMap {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (S : Subalgebra R A) {x : R} (h : IsSMulRegular A (algebraMap R A x)) :
    IsSMulRegular S (algebraMap R S x) := by
  rw [IsSMulRegular] at h ⊢
  intro y z hyz
  apply Subtype.ext
  apply h
  have h2 : algebraMap R S x * y = algebraMap R S x * z := by
    simpa [smul_eq_mul] using hyz
  have h3 := congrArg (Subtype.val) h2
  simpa using h3

/-! ## The `W♭`-algebra structure of the chart -/

/-- **`(p : R_S) = 0`** for the perfected tilted chart: it is a `PreTilt W p`-subalgebra and
`p = 0` in `PreTilt W p`. -/
theorem chart_p_eq_zero {ι : Type} [DecidableEq ι] (Q : PerfectoidData p W) (t : ι → W)
    (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k)
    (j₀ : ι) (e : ℕ) (S : Finset ι) :
    (p : tiltChart Q t tr htr0 htr j₀ e S) = 0 := by
  rw [← map_natCast (algebraMap (PreTilt W p) (tiltChart Q t tr htr0 htr j₀ e S)) p,
    CharP.cast_eq_zero, map_zero]

/-- **`φ_S(ϖ♭)` is a non-zero-divisor of the chart `R_S`.**  `ϖ♭` is a non-zero-divisor of
`W♭ = PreTilt W p` (`Work.DSM5c.Regularity.tiltVarpi_isSMulRegular`), hence so is its image in the
localisation `(W♭)_{u_S}` (`IsSMulRegular.of_isLocalization`), hence so is the image in the
subalgebra `R_S ⊆ (W♭)_{u_S}` (`isSMulRegular_subalgebra_algebraMap`). -/
theorem chartPhi_tiltVarpi_isSMulRegular {ι : Type} [DecidableEq ι] (Q : PerfectoidData p W)
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι) :
    IsSMulRegular (tiltChart Q t tr htr0 htr j₀ e S)
      (chartPhi Q t tr htr0 htr j₀ e S (tiltVarpi Q)) := by
  have hreg : IsSMulRegular (PreTilt W p) (tiltVarpi Q) := by
    rw [IsSMulRegular]
    intro x y hxy
    have h : tiltVarpi Q * (x - y) = 0 := by
      rw [mul_sub, show tiltVarpi Q * x = tiltVarpi Q * y from by
        simpa [smul_eq_mul] using hxy, sub_self]
    exact sub_eq_zero.mp (Work.DSM5c.Regularity.tiltVarpi_isSMulRegular Q (x - y) h)
  have hloc : IsSMulRegular (Localization.Away (tS (chartTiltGen Q t tr htr0 htr j₀ e) S))
      (algebraMap (PreTilt W p) _ (tiltVarpi Q)) :=
    IsSMulRegular.of_isLocalization
      (Localization.Away (tS (chartTiltGen Q t tr htr0 htr j₀ e) S))
      (Submonoid.powers (tS (chartTiltGen Q t tr htr0 htr j₀ e) S)) hreg
  exact isSMulRegular_subalgebra_algebraMap (tiltChart Q t tr htr0 htr j₀ e S) hloc

/-! ## The ideal identity `I = (ξ') + p·I` -/

/-- **The ideal `I = 𝕎R·𝕎(φ)(ker θ_W)` satisfies `I = (ξ') + p·I`.**  Every generator `𝕎φ(k)`,
`k ∈ ker θ_W`, is `[φ b]·ξ' + p·𝕎φ(u)` with `u ∈ ker θ_W` (the delegated
`Work.DSM5c.G2.kerTheta_decomp`), so `I = (ξ') + p·I`. -/
theorem span_map_ker_fontaineTheta_eq_xiR_add_mul (Q : PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (v : Wˣ) (hv : Q.ϖ 0 ^ p = (p : W) * (v : W))
    (z₀ : WittVector p (PreTilt W p))
    (hz₀ : WittVector.fontaineTheta (p := p) (R := W) z₀ = (v : W))
    {R : Type} [CommRing R] (φ : PreTilt W p →+* R) :
    kerIdeal φ = Ideal.span {xiR Q φ z₀} +
      Ideal.span {(p : WittVector p R)} * kerIdeal φ := by
  classical
  apply le_antisymm
  · -- `I ≤ (ξ') + p·I`: it suffices to check the generators of `I`
    rw [kerIdeal, Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨b, u, hu, hkdecomp⟩ := kerTheta_decomp (p := p) (W := W) Q hθ v hv z₀ hz₀ hk
    have hmapξ : WittVector.map φ
        (WittVector.teichmuller p (tiltVarpi Q ^ p) - (p : WittVector p (PreTilt W p)) * z₀)
        = xiR Q φ z₀ :=
      map_xiChart Q φ z₀
    rw [hkdecomp, map_add, map_mul, map_mul, hmapξ, map_natCast]
    refine Submodule.mem_sup.mpr ⟨WittVector.map φ (WittVector.teichmuller p b) * xiR Q φ z₀,
      Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _),
      (p : WittVector p R) * WittVector.map φ u,
      Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _)
        (Ideal.subset_span ⟨u, hu, rfl⟩),
      rfl⟩
  · -- `(ξ') + p·I ≤ I`
    refine add_le ?_ ?_
    · rw [Ideal.span_singleton_le_iff_mem]
      exact Ideal.subset_span
        ⟨xiChart Q z₀, fontaineTheta_xiChart Q v hv z₀ hz₀, map_xiChart Q φ z₀⟩
    · exact Ideal.mul_le_right

/-! ## The main step: `untiltOf R φ` is `p`-torsion-free -/

/-- **`p`-torsion-freeness of the untilt `untiltOf R φ = 𝕎R ⧸ 𝕎(φ)(ker θ_W)`**, for a perfect
characteristic-`p` `W♭`-algebra `R` on which `φ(ϖ♭)^p` is a non-zero-divisor.

The non-degenerate case reduces to `(I : p) = I` for `I = 𝕎(φ)(ker θ_W)`, which follows from
`span_map_ker_fontaineTheta_eq_xiR_add_mul` and the `p`-torsion-freeness of `𝕎R ⧸ (ξ')`
(`Work.DSM5c.G2.quotTeichmullerSubPz_torsionFree`); the degenerate case (`R` of characteristic one,
i.e. the zero ring) is trivial because then `𝕎R` — and hence the quotient — is a subsingleton. -/
theorem isSMulRegular_untiltOf_of_regular {R : Type} [CommRing R] [PerfectRing R p]
    (Q : PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (φ : PreTilt W p →+* R) (hp0 : (p : R) = 0)
    (hc : IsSMulRegular R (φ (tiltVarpi Q) ^ p)) :
    IsSMulRegular (untiltOf (p := p) (W := W) R φ) (p : untiltOf (p := p) (W := W) R φ) := by
  classical
  by_cases hsub : Subsingleton R
  · -- degenerate case: `𝕎 R`, and hence every quotient of it, is a subsingleton
    haveI : Subsingleton (WittVector p R) :=
      ⟨fun x y => WittVector.ext fun n => Subsingleton.elim _ _⟩
    haveI : Subsingleton (WittVector p R ⧸ kerIdeal φ) :=
      ⟨fun x y => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [Subsingleton.elim a b]⟩
    exact fun x y _ => Subsingleton.elim x y
  · -- non-degenerate case: `R` has characteristic `p`
    haveI hchar : CharP R p := by
      have hdvd : ringChar R ∣ p := ringChar.dvd hp0
      rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd (ringChar R) hdvd with h1 | hp
      · exact absurd (ringChar.ringChar_eq_one.mp h1) hsub
      · exact ringChar.of_eq hp
    obtain ⟨v, hv⟩ := Q.unit
    obtain ⟨z₀, hz₀⟩ := hθ (v : W)
    have hIeq : kerIdeal φ = Ideal.span {xiR Q φ z₀} +
        Ideal.span {(p : WittVector p R)} * kerIdeal φ :=
      span_map_ker_fontaineTheta_eq_xiR_add_mul Q hθ v hv z₀ hz₀ φ
    have hcreg : ∀ x : R, (φ (tiltVarpi Q) ^ p) * x = 0 → x = 0 := by
      intro x hx
      rw [IsSMulRegular] at hc
      exact hc (by simpa [smul_eq_mul] using hx)
    -- `p`-torsion-freeness of `𝕎R ⧸ (ξ')`
    have hA : IsSMulRegular (WittVector p R ⧸ Ideal.span {xiR Q φ z₀})
        (p : WittVector p R ⧸ Ideal.span {xiR Q φ z₀}) :=
      quotTeichmullerSubPz_torsionFree (p := p) (φ (tiltVarpi Q) ^ p) hcreg
        (WittVector.map φ z₀)
    rw [IsSMulRegular] at hA
    have hle : Ideal.span {xiR Q φ z₀} ≤ kerIdeal φ :=
      Ideal.span_singleton_le_iff_mem _ |>.mpr
        (Ideal.subset_span
          ⟨xiChart Q z₀, fontaineTheta_xiChart Q v hv z₀ hz₀, map_xiChart Q φ z₀⟩)
    -- `(I : p) ⊆ I`
    have hIp : ∀ y : WittVector p R, (p : WittVector p R) * y ∈ kerIdeal φ → y ∈ kerIdeal φ := by
      intro y hy
      rw [hIeq] at hy
      obtain ⟨a, ha, i, hi, hai⟩ := Submodule.mem_sup.mp hy
      obtain ⟨i₁, hi₁, hii⟩ := Ideal.mem_span_singleton_mul.mp hi
      have ha' : (p : WittVector p R) * (y - i₁) = a := by
        rw [mul_sub, hii, ← hai]
        abel
      have hmem : (p : WittVector p R) * (y - i₁) ∈ Ideal.span {xiR Q φ z₀} := by
        rw [ha']
        exact ha
      have hzero : (p : WittVector p R ⧸ Ideal.span {xiR Q φ z₀}) •
          Ideal.Quotient.mk (Ideal.span {xiR Q φ z₀}) (y - i₁) = 0 := by
        rw [smul_eq_mul,
          ← map_natCast (Ideal.Quotient.mk (Ideal.span {xiR Q φ z₀})) p, ← map_mul,
          Ideal.Quotient.eq_zero_iff_mem]
        exact hmem
      have hdiff : Ideal.Quotient.mk (Ideal.span {xiR Q φ z₀}) (y - i₁) = 0 := by
        refine hA ?_
        simp only [hzero, smul_zero]
      have hsubI : y - i₁ ∈ kerIdeal φ :=
        hle (Ideal.Quotient.eq_zero_iff_mem.mp hdiff)
      have hyi : y = (y - i₁) + i₁ := by abel
      rw [hyi]
      exact Ideal.add_mem _ hsubI hi₁
    have hmain : IsSMulRegular (WittVector p R ⧸ kerIdeal φ) (p : WittVector p R ⧸ kerIdeal φ) := by
      have h := isSMulRegular_quotient_of_mul_mem (kerIdeal φ) (p : WittVector p R) hIp
      simpa using h
    exact hmain

/-! ## The chart untilt is `p`-torsion-free -/

/-- **Gap G2 of the M5c node** (`Submission/Work/DSM5c/NOTES.md` §20.3): the chart untilt
`D_S = Work.DSM5c.untiltOf R_S φ_S = 𝕎 R_S ⧸ 𝕎(φ_S)(ker θ_W)` is `p`-torsion-free.

This is the hypothesis `hreg` of the dévissage `Work.DSM5c.almostAcyc_span_pow` (which upgrades
almost acyclicity modulo `(p)` to almost acyclicity modulo `(p ^ m)` for every `m`), applied
termwise to the Čech complex `Č(Dp)` — whose terms are finite products of the `D_S`.

For the *ξ*-form untilt `𝕎 R ⧸ ([w] - p)` this is already proved in
`Submission/Work/DSM5c/Untilt/untilt_p_torsionFree.lean`
(`Work.DSM5c.Untilt.untilt_p_torsionFree`), under the hypothesis that `w` is a non-zero-divisor of
`R`.  The charts, however, use the *ideal*-form untilt `𝕎 R_S ⧸ 𝕎(φ_S)(ker θ_W)` (the ideal form
avoids having to name a generator of `ker θ_W`; see NOTES §20.1 and `ChartComparison.lean`, where
the mod-`p` comparison `Work.DSM5c.mem_span_p_sup_map_ker_fontaineTheta`
(`x ∈ (p) ⊔ 𝕎(φ)(ker θ_W) ↔ constantCoeff x ∈ (φ (ϖ♭))^p`) is proved *without* principality).

Useful facts for the prover: `u_S = ∏_{i ∈ S} u_i` (with `u = Work.DSM5c.chartTiltGen …`) is a
non-zero-divisor of `R_S`, because `R_S` is a subring of the localisation `(W♭)_{u_S}` in which
`u_S` is a unit (`Work.DSM5c.tiltChart`); and `♯(u_S) = t_S`.  For `W = ℤ_p^{cycl}`, `S = {j₀}`,
`R_S = W♭`, `D_S = W`, this is `Q.torsionFree`.  A route that would suffice: the tilt
identification for the *chart* untilt, `PreTilt (untiltOf R_S φ_S) p ≅ R_S` (the `R_S`-analogue of
`Work.DSM5c.toPerfectionEquiv` in `Submission/Work/DSM5c/Untilt/Tilt.lean`), since `p`-torsion in
`D_S` corresponds to `ϖ♭`-torsion in `R_S`, which is zero. -/
theorem isSMulRegular_chartUntilt {p : ℕ} [Fact p.Prime] {W : Type} [CommRing W]
    [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type} [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (hj₀ : t j₀ = Q.ϖ 0 ^ e)
    (S : Finset ι) :
    IsSMulRegular (Work.DSM5c.untiltOf (p := p) (W := W)
        (Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e S)
        (Work.DSM5c.chartPhi Q t tr htr0 htr j₀ e S))
      (p : Work.DSM5c.untiltOf (p := p) (W := W)
        (Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e S)
        (Work.DSM5c.chartPhi Q t tr htr0 htr j₀ e S)) := by
  have hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)) :=
    surjective_fontaineTheta_of_perfectoidData Q
  haveI hperf : PerfectRing (Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e S) p :=
    Work.DSM5c.Charts.perfChartRing_perfect p (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) S
  refine isSMulRegular_untiltOf_of_regular (p := p) (W := W)
    (R := Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e S) Q hθ
    (Work.DSM5c.chartPhi Q t tr htr0 htr j₀ e S) (chart_p_eq_zero Q t tr htr0 htr j₀ e S) ?_
  exact (chartPhi_tiltVarpi_isSMulRegular Q t tr htr0 htr j₀ e S).pow p

end Work.DSM5c.G2
