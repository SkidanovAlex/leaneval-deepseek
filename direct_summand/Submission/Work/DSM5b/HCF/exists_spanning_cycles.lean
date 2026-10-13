import Mathlib
import Submission.Work.DSM5b.HCF.Complex

universe u

namespace Work.DSM5b.HCF

open CategoryTheory

/-- Finite generation of an `R`-module transfers along an isomorphism of `R`-modules. -/
lemma moduleFinite_of_iso {R : Type u} [CommRing R] {P Q : ModuleCat.{u} R} (e : P ≅ Q)
    (h : Module.Finite R P) : Module.Finite R Q := by
  have := h
  exact Module.Finite.of_surjective e.hom.hom
    (ConcreteCategory.bijective_of_isIso e.hom).2

/-- **Finitely generated homology gives finitely many cycles spanning it** (short complex form).

Let `S : X₁ ⟶ X₂ ⟶ X₃` be a short complex of `R`-modules whose homology `H = ker(g)/im(f)` is a
finitely generated `R`-module.  Then there are finitely many cycles `f i ∈ ker g` such that every
cycle `z` is a linear combination of the `f i` modulo a boundary: `z = ∑ c i • f i + f y`.

Proof.  Mathlib's `ShortComplex.moduleCatHomologyIso` identifies `S.homology` with the concrete
quotient `ker S.g ⧸ range S.moduleCatToCycles`, where `S.moduleCatToCycles` is `S.f` with values in
`ker S.g`.  Hence the quotient is finitely generated; taking a finite generating family
`ker S.g ⧸ range S.moduleCatToCycles` and lifting each generator along the surjective quotient map
`Submodule.mkQ` to an element `w i ∈ ker S.g` produces the cycles, and two classes are equal in the
quotient exactly when they differ by an element of `range S.moduleCatToCycles`, i.e. by a boundary
`S.f y`. -/
lemma exists_spanning_cycles_short {R : Type u} [CommRing R] (S : ShortComplex (ModuleCat.{u} R))
    (h : Module.Finite R S.homology) :
    ∃ (k : ℕ) (f : Fin k → S.X₂),
      (∀ i, S.g (f i) = 0) ∧
      ∀ z : S.X₂, S.g z = 0 →
        ∃ c : Fin k → R, ∃ y : S.X₁, z = (∑ i, c i • f i) + S.f y := by
  classical
  -- the concrete description of the homology as `ker S.g ⧸ im S.f`, and finiteness of the quotient
  have hsurj : Function.Surjective (ShortComplex.moduleCatHomologyIso S).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (ShortComplex.moduleCatHomologyIso S).hom).2
  have : Module.Finite R (ModuleCat.of R (S.g.hom.ker ⧸ S.moduleCatToCycles.range)) :=
    Module.Finite.of_surjective (ShortComplex.moduleCatHomologyIso S).hom.hom hsurj
  obtain ⟨k, g, hg⟩ :=
    Module.Finite.exists_fin (R := R)
      (M := ModuleCat.of R (S.g.hom.ker ⧸ S.moduleCatToCycles.range))
  -- lift the generators to actual cycles
  have hw : ∀ i, ∃ w : S.g.hom.ker, Submodule.mkQ _ w = g i := fun i =>
    Submodule.mkQ_surjective _ (g i)
  choose w hw using hw
  refine ⟨k, fun i => (w i : S.X₂), ?_, ?_⟩
  · intro i
    simp
  · intro z hz
    have hzk : z ∈ S.g.hom.ker := LinearMap.mem_ker.mpr hz
    have hzmem : Submodule.mkQ S.moduleCatToCycles.range ⟨z, hzk⟩ ∈
        Submodule.span R (Set.range g) := by
      rw [hg]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun R] at hzmem
    obtain ⟨c, hc⟩ := hzmem
    -- the class of `z` agrees with the class of the lifted combination
    have h1 : Submodule.mkQ S.moduleCatToCycles.range (∑ i, c i • w i)
        = Submodule.mkQ S.moduleCatToCycles.range ⟨z, hzk⟩ := by
      calc Submodule.mkQ S.moduleCatToCycles.range (∑ i, c i • w i)
          = ∑ i, c i • Submodule.mkQ S.moduleCatToCycles.range (w i) := by
            rw [map_sum]
            simp
        _ = ∑ i, c i • g i := by simp [hw]
        _ = Submodule.mkQ S.moduleCatToCycles.range ⟨z, hzk⟩ := hc
    -- hence the difference is a boundary
    have h2 : (⟨z, hzk⟩ : S.g.hom.ker) - ∑ i, c i • w i ∈ S.moduleCatToCycles.range :=
      (Submodule.Quotient.eq _).mp (by simpa only [Submodule.mkQ_apply] using h1.symm)
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp h2
    refine ⟨c, y, ?_⟩
    have hy' : S.f y = z - ∑ i, c i • (w i : S.X₂) := by
      have h3 := congrArg Subtype.val hy
      simp only [ShortComplex.moduleCatToCycles, Submodule.coe_sub,
        Submodule.coe_sum, Submodule.coe_smul] at h3
      exact h3
    rw [hy']
    abel

/-- **From finite generation of the cohomology to finitely many cycles spanning it.**  If the
`(q+1)`-st cohomology of the honest tuple complex of a coefficient system `𝒜`
(`Work.DSM5b.htcComplex`, i.e. `𝒜.Htc (q+1)` modulo `𝒜.htcD q`) is a finitely generated
`R`-module, then there are finitely many cycles `f i` such that every cycle is a linear combination
of the `f i` plus a boundary.

Route: identify `(htcComplex 𝒜).homology (q+1)` with
`(cycles (q+1)) ⧸ (boundaries (q+1))` (Mathlib: `HomologicalComplex.cycles`/`boundaries`, the
`ShortComplex` API, with `Work.DSM5b.htcComplex_d` giving the differentials `𝒜.htcD _`), use
`Module.Finite.fg_top` (or `Module.Finite.exists_fin`) to get a finite generating family of the
quotient, lift each generator along the (surjective) quotient map `Submodule.mkQ` to a cycle
(`Submodule.mkQ_surjective`), and conclude since two cycles have the same class in the quotient
exactly when they differ by an element of the boundary submodule. -/
theorem exists_spanning_cycles {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι]
    (𝒜 : Work.DSM5b.CoeffSys R ι) (q : ℕ)
    (h : Module.Finite R ((Work.DSM5b.htcComplex 𝒜).homology (q + 1))) :
    ∃ (k : ℕ) (f : Fin k → 𝒜.Htc (q + 1)),
      (∀ i, 𝒜.htcD (q + 1) (f i) = 0) ∧
      ∀ z : 𝒜.Htc (q + 1), 𝒜.htcD (q + 1) z = 0 →
        ∃ c : Fin k → R, ∃ y : 𝒜.Htc q, z = (∑ i, c i • f i) + 𝒜.htcD q y := by
  classical
  -- the short complex `X q ⟶ X (q+1) ⟶ X (q+2)` of the honest tuple complex
  have hi : (ComplexShape.up ℕ).prev (q + 1) = q :=
    ComplexShape.prev_eq' (ComplexShape.up ℕ) (ComplexShape.up_mk q (q + 1) rfl)
  have hk : (ComplexShape.up ℕ).next (q + 1) = q + 2 :=
    ComplexShape.next_eq' (ComplexShape.up ℕ) (ComplexShape.up_mk (q + 1) (q + 2) rfl)
  -- its homology is the `(q+1)`-st homology of the complex
  have hfin : Module.Finite R ((htcComplex 𝒜).sc' q (q + 1) (q + 2)).homology :=
    moduleFinite_of_iso ((htcComplex 𝒜).homologyIsoSc' q (q + 1) (q + 2) hi hk) h
  obtain ⟨k, f, hf, hsp⟩ := exists_spanning_cycles_short _ hfin
  -- its two maps are the differentials `𝒜.htcD q` and `𝒜.htcD (q+1)`
  have hSg : ((htcComplex 𝒜).sc' q (q + 1) (q + 2)).g = ModuleCat.ofHom (𝒜.htcD (q + 1)) :=
    htcComplex_d 𝒜 (q + 1)
  have hSf : ((htcComplex 𝒜).sc' q (q + 1) (q + 2)).f = ModuleCat.ofHom (𝒜.htcD q) :=
    htcComplex_d 𝒜 q
  rw [hSg] at hf
  refine ⟨k, fun i => (f i : 𝒜.Htc (q + 1)), ?_, ?_⟩
  · intro i
    exact hf i
  · intro z hz
    have hz' : ((htcComplex 𝒜).sc' q (q + 1) (q + 2)).g z = 0 := by
      rw [hSg]
      exact hz
    obtain ⟨c, y, hy⟩ := hsp z hz'
    refine ⟨c, (y : 𝒜.Htc q), ?_⟩
    rw [hSf] at hy
    exact hy

end Work.DSM5b.HCF
