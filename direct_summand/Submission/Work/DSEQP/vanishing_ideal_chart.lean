import Mathlib

namespace Work.DSEQP

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

/-!
# `Work.DSEQP.vanishing_ideal_chart`

Auxiliary lemmas (about homogeneous localizations, and about the chart ideals of the ideal sheaf
of a closed subscheme of `Proj`) and then the chart-saturation statement itself.
-/

/-- The standard grading of `MvPolynomial (Fin n) A`. -/
abbrev StdGrading (A : Type*) [CommRing A] (n : ℕ) : ℕ → Submodule A (MvPolynomial (Fin n) A) :=
  MvPolynomial.homogeneousSubmodule (Fin n) A

/-- The variable `X j` lies in the degree-one graded piece. -/
lemma isHomogeneous_X_mem (A : Type*) [CommRing A] (n : ℕ) (j : Fin n) :
    MvPolynomial.X j ∈ StdGrading A n 1 := MvPolynomial.isHomogeneous_X A j

section AwayLemmas

variable {S : Type*} [CommRing S] {σ : Type*} [SetLike σ S] [AddSubgroupClass σ S]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- `f^n / f^n = 1` in the homogeneous localization away from `f`. -/
lemma away_mk_self {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) (n : ℕ) :
    Away.mk 𝒜 hf n (f ^ n) (SetLike.pow_mem_graded n hf) = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, HomogeneousLocalization.val_one]
  exact Localization.mk_self (S := Submonoid.powers f) ⟨f ^ n, n, rfl⟩

/-- Multiplicativity of `Away.mk` in its numerator. -/
lemma away_mk_mul {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) (k l : ℕ) (a b : S)
    (ha : a ∈ 𝒜 (k • d)) (hb : b ∈ 𝒜 (l • d)) :
    Away.mk 𝒜 hf k a ha * Away.mk 𝒜 hf l b hb =
      Away.mk 𝒜 hf (k + l) (a * b)
        (by rw [add_smul]; exact SetLike.mul_mem_graded ha hb) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, Away.val_mk, Away.val_mk, Away.val_mk, Localization.mk_mul]
  congr 1
  exact Subtype.ext (by simp [pow_add])

/-- The "padding" identity `a/f^k = (a f^l)/f^(k+l)`. -/
lemma away_mk_pad {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) (k l : ℕ) (a : S)
    (ha : a ∈ 𝒜 (k • d)) :
    Away.mk 𝒜 hf k a ha =
      Away.mk 𝒜 hf (k + l) (a * f ^ l)
        (by rw [add_smul]; exact SetLike.mul_mem_graded ha (SetLike.pow_mem_graded l hf)) := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, Away.val_mk]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  rw [pow_add]
  ring

/-- Congruence for `Away.mk` in the exponent and in the numerator. -/
lemma away_mk_congr {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) {n n' : ℕ} {a a' : S} (hn : n = n')
    (haa : a = a') (ha : a ∈ 𝒜 (n • d)) (ha' : a' ∈ 𝒜 (n' • d)) :
    Away.mk 𝒜 hf n a ha = Away.mk 𝒜 hf n' a' ha' := by
  subst hn; subst haa; rfl

/-- Powers of `Away.mk`. -/
lemma away_mk_pow {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) {g : S} (hg : g ∈ 𝒜 d) (n : ℕ) :
    (Away.mk 𝒜 hf 1 (g ^ 1) (by simpa using hg)) ^ n =
      Away.mk 𝒜 hf n (g ^ n) (SetLike.pow_mem_graded n hg) := by
  induction n with
  | zero => simpa using (away_mk_self (𝒜 := 𝒜) hf 0).symm
  | succ n ih =>
    rw [pow_succ, ih, away_mk_mul (𝒜 := 𝒜) hf n 1 (g ^ n) (g ^ 1)
      (SetLike.pow_mem_graded n hg) (by simpa using hg)]
    exact away_mk_congr hf rfl (by rw [pow_one, ← pow_succ]) _ _

/-- `Away.mk` of the product form: `a/f^k · (g/f)^m = (a g^m)/f^(k+m)`. -/
lemma away_mk_mul_pow {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) {g : S} (hg : g ∈ 𝒜 d) (k m : ℕ) (a : S)
    (ha : a ∈ 𝒜 (k • d)) :
    Away.mk 𝒜 hf k a ha * (Away.mk 𝒜 hf 1 (g ^ 1) (by simpa using hg)) ^ m =
      Away.mk 𝒜 hf (k + m) (a * g ^ m)
        (by rw [add_smul]; exact SetLike.mul_mem_graded ha (SetLike.pow_mem_graded m hg)) := by
  rw [away_mk_pow (𝒜 := 𝒜) hf hg m,
    away_mk_mul (𝒜 := 𝒜) hf k m a (g ^ m) ha (SetLike.pow_mem_graded m hg)]

/-- Membership in the graded piece of a product with a power. -/
lemma mem_add_smul_pow {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) {a : S} {k : ℕ} (ha : a ∈ 𝒜 (k • d))
    (m : ℕ) : a * f ^ m ∈ 𝒜 ((k + m) • d) := by
  rw [add_smul]
  exact SetLike.mul_mem_graded ha (SetLike.pow_mem_graded m hf)

/-- The key fraction identity: in `Away 𝒜 (X * Y)`, the two localizations of `a/X^k` and of
`a/Y^k` differ by the factor `X^(2k)`. -/
lemma away_mk_swap {X Y : S} (hX : X ∈ 𝒜 1) (hY : Y ∈ 𝒜 1)
    (k : ℕ) (a : S) (ha : a ∈ 𝒜 (k • 1)) :
    Away.mk 𝒜 (f := X*Y) (d := 2) (by simpa using SetLike.mul_mem_graded hX hY) k (a * X ^ k)
        (by simpa [smul_eq_mul, Nat.mul_two] using
          SetLike.mul_mem_graded ha (SetLike.pow_mem_graded k hX)) =
      Away.mk 𝒜 (f := X*Y) (d := 2) (by simpa using SetLike.mul_mem_graded hX hY) k (X ^ (2 * k))
        (by simpa [smul_eq_mul, Nat.mul_two, two_mul] using SetLike.pow_mem_graded (2*k) hX) *
      Away.mk 𝒜 (f := X*Y) (d := 2) (by simpa using SetLike.mul_mem_graded hX hY) k (a * Y ^ k)
        (by simpa [smul_eq_mul, Nat.mul_two] using
          SetLike.mul_mem_graded ha (SetLike.pow_mem_graded k hY)) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, Away.val_mk, Away.val_mk, Away.val_mk, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  rw [mul_pow]
  ring

end AwayLemmas

section Transport

variable {S : Type*} [CommRing S] {σ : Type*} [SetLike σ S] [AddSubgroupClass σ S]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- The two chart ideals of an ideal sheaf on `Proj`, localised to `D₊(F·G)`, agree. -/
lemma chart_transport {Y : Scheme}
    (i : Y ⟶ Proj 𝒜) {F G : S} (hF : F ∈ 𝒜 1) (hG : G ∈ 𝒜 1) :
    (((i.ker.ideal ⟨Proj.basicOpen 𝒜 F, Proj.isAffineOpen_basicOpen 𝒜 F hF (by norm_num)⟩)).comap
        (CommRingCat.Hom.hom (Proj.basicOpenIsoAway 𝒜 F hF (by norm_num)).hom)).map
      (awayMap 𝒜 hG (show F*G = F*G from rfl)) =
    (((i.ker.ideal ⟨Proj.basicOpen 𝒜 G, Proj.isAffineOpen_basicOpen 𝒜 G hG (by norm_num)⟩)).comap
        (CommRingCat.Hom.hom (Proj.basicOpenIsoAway 𝒜 G hG (by norm_num)).hom)).map
      (awayMap 𝒜 hF (show F*G = G*F from mul_comm F G)) := by
  have hFG : F*G ∈ 𝒜 2 := by simpa using SetLike.mul_mem_graded hF hG
  let W : (Proj 𝒜).affineOpens :=
    ⟨Proj.basicOpen 𝒜 (F*G), Proj.isAffineOpen_basicOpen 𝒜 (F*G) hFG (by norm_num)⟩
  let Vf : (Proj 𝒜).affineOpens :=
    ⟨Proj.basicOpen 𝒜 F, Proj.isAffineOpen_basicOpen 𝒜 F hF (by norm_num)⟩
  let Vg : (Proj 𝒜).affineOpens :=
    ⟨Proj.basicOpen 𝒜 G, Proj.isAffineOpen_basicOpen 𝒜 G hG (by norm_num)⟩
  let φf : (Away 𝒜 F) →+* Γ(Proj 𝒜, Proj.basicOpen 𝒜 F) :=
    CommRingCat.Hom.hom (Proj.basicOpenIsoAway 𝒜 F hF (by norm_num)).hom
  let φg : (Away 𝒜 G) →+* Γ(Proj 𝒜, Proj.basicOpen 𝒜 G) :=
    CommRingCat.Hom.hom (Proj.basicOpenIsoAway 𝒜 G hG (by norm_num)).hom
  let ψ : (Away 𝒜 (F*G)) →+* Γ(Proj 𝒜, Proj.basicOpen 𝒜 (F*G)) :=
    CommRingCat.Hom.hom (Proj.basicOpenIsoAway 𝒜 (F*G) hFG (by norm_num)).hom
  have hsurjψ : Function.Surjective ψ :=
    (ConcreteCategory.bijective_of_isIso (Proj.basicOpenIsoAway 𝒜 (F*G) hFG (by norm_num)).hom).2
  have hinjψ : Function.Injective ψ :=
    (ConcreteCategory.bijective_of_isIso (Proj.basicOpenIsoAway 𝒜 (F*G) hFG (by norm_num)).hom).1
  have hsurjφg : Function.Surjective φg :=
    (ConcreteCategory.bijective_of_isIso (Proj.basicOpenIsoAway 𝒜 G hG (by norm_num)).hom).2
  have hsurjφf : Function.Surjective φf :=
    (ConcreteCategory.bijective_of_isIso (Proj.basicOpenIsoAway 𝒜 F hF (by norm_num)).hom).2
  have hkerψ : Ideal.comap ψ ⊥ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Ideal.mem_comap, Ideal.mem_bot] at hy
    exact hinjψ (by rw [hy, map_zero])
  have hWf : W ≤ Vf := by
    show Proj.basicOpen 𝒜 (F*G) ≤ Proj.basicOpen 𝒜 F
    rw [Proj.basicOpen_mul]; exact inf_le_left
  have hWg : W ≤ Vg := by
    show Proj.basicOpen 𝒜 (F*G) ≤ Proj.basicOpen 𝒜 G
    rw [Proj.basicOpen_mul]; exact inf_le_right
  change ((i.ker.ideal Vf).comap φf).map (awayMap 𝒜 hG (show F*G = F*G from rfl)) =
    ((i.ker.ideal Vg).comap φg).map (awayMap 𝒜 hF (show F*G = G*F from mul_comm F G))
  let ρf : Γ(Proj 𝒜, Proj.basicOpen 𝒜 F) →+* Γ(Proj 𝒜, Proj.basicOpen 𝒜 (F*G)) :=
    CommRingCat.Hom.hom ((Proj 𝒜).presheaf.map (homOfLE hWf).op)
  let ρg : Γ(Proj 𝒜, Proj.basicOpen 𝒜 G) →+* Γ(Proj 𝒜, Proj.basicOpen 𝒜 (F*G)) :=
    CommRingCat.Hom.hom ((Proj 𝒜).presheaf.map (homOfLE hWg).op)
  have hhomf : (homOfLE (Proj.basicOpen_mono 𝒜 F (F*G) ⟨G, rfl⟩) :
      Proj.basicOpen 𝒜 (F*G) ⟶ Proj.basicOpen 𝒜 F) = homOfLE hWf := rfl
  have hhomg : (homOfLE (Proj.basicOpen_mono 𝒜 G (F*G) ⟨F, mul_comm F G⟩) :
      Proj.basicOpen 𝒜 (F*G) ⟶ Proj.basicOpen 𝒜 G) = homOfLE hWg := rfl
  have hsqf : ψ.comp (awayMap 𝒜 hG (show F*G = F*G from rfl)) = ρf.comp φf := by
    have h := Proj.awayMap_awayToSection (𝒜 := 𝒜) (f := F) (g := G) hG (x := F*G) rfl
    rw [← Proj.basicOpenIsoAway_hom (𝒜 := 𝒜) (f := F*G) hFG (show 0 < 2 by norm_num),
        ← Proj.basicOpenIsoAway_hom (𝒜 := 𝒜) (f := F) hF (show 0 < 1 by norm_num)] at h
    have h2 := congrArg CommRingCat.Hom.hom h
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h2
    rw [hhomf] at h2
    exact h2
  have hsqg : ψ.comp (awayMap 𝒜 hF (show F*G = G*F from mul_comm F G)) = ρg.comp φg := by
    have h := Proj.awayMap_awayToSection (𝒜 := 𝒜) (f := G) (g := F) hF (x := F*G) (mul_comm F G)
    rw [← Proj.basicOpenIsoAway_hom (𝒜 := 𝒜) (f := F*G) hFG (show 0 < 2 by norm_num),
        ← Proj.basicOpenIsoAway_hom (𝒜 := 𝒜) (f := G) hG (show 0 < 1 by norm_num)] at h
    have h2 := congrArg CommRingCat.Hom.hom h
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h2
    rw [hhomg] at h2
    exact h2
  have keyf : ((i.ker.ideal Vf).comap φf).map (awayMap 𝒜 hG (show F*G = F*G from rfl)) =
      (i.ker.ideal W).comap ψ := by
    have h1 : Ideal.map ψ (Ideal.map (awayMap 𝒜 hG (show F*G = F*G from rfl))
        (Ideal.comap φf (i.ker.ideal Vf))) = i.ker.ideal W := by
      rw [Ideal.map_map, hsqf, ← Ideal.map_map, Ideal.map_comap_of_surjective _ hsurjφf]
      exact Scheme.IdealSheafData.map_ideal i.ker hWf
    rw [← h1, Ideal.comap_map_of_surjective ψ hsurjψ, hkerψ, sup_bot_eq]
  have keyg : ((i.ker.ideal Vg).comap φg).map (awayMap 𝒜 hF (show F*G = G*F from mul_comm F G)) =
      (i.ker.ideal W).comap ψ := by
    have h1 : Ideal.map ψ (Ideal.map (awayMap 𝒜 hF (show F*G = G*F from mul_comm F G))
        (Ideal.comap φg (i.ker.ideal Vg))) = i.ker.ideal W := by
      rw [Ideal.map_map, hsqg, ← Ideal.map_map, Ideal.map_comap_of_surjective _ hsurjφg]
      exact Scheme.IdealSheafData.map_ideal i.ker hWg
    rw [← h1, Ideal.comap_map_of_surjective ψ hsurjψ, hkerψ, sup_bot_eq]
  rw [keyf, keyg]

end Transport

/-- The localisation criterion for ideals: if `algebraMap v` lies in the extension of `I`, then some
power of the localising element times `v` lies in `I`. -/
lemma exists_pow_mul_mem_of_algebraMap_mem_map {R S' : Type*} [CommRing R] [CommRing S']
    [Algebra R S'] (t : R) [IsLocalization.Away t S'] {I : Ideal R} {v : R}
    (h : algebraMap R S' v ∈ I.map (algebraMap R S')) : ∃ m : ℕ, t ^ m * v ∈ I := by
  obtain ⟨m, hm, hm2⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers t) S' I v).mp h
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff m t).mp hm
  exact ⟨n, by rw [hn]; exact hm2⟩

theorem vanishing_ideal_chart (A : Type*) [CommRing A] (n : ℕ) (X : Scheme)
    (i : X ⟶ AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin n) A))
    [AlgebraicGeometry.IsClosedImmersion i] (j : Fin n)
    (z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) A)
          (MvPolynomial.X j))
    (hz : Ideal.Quotient.mk (i.ker.ideal
        ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) A) (MvPolynomial.X j),
          Proj.isAffineOpen_basicOpen _ (MvPolynomial.X j)
            (MvPolynomial.isHomogeneous_X A j) (by norm_num)⟩)
        ((Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin n) A) (MvPolynomial.X j)
          (MvPolynomial.isHomogeneous_X A j) (by norm_num)).hom z) = 0) :
    ∃ (k : ℕ) (g : MvPolynomial (Fin n) A)
      (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin n) A k),
      (∀ j' : Fin n, Ideal.Quotient.mk (i.ker.ideal
          ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) A) (MvPolynomial.X j'),
            Proj.isAffineOpen_basicOpen _ (MvPolynomial.X j')
              (MvPolynomial.isHomogeneous_X A j') (by norm_num)⟩)
          ((Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin n) A) (MvPolynomial.X j')
            (MvPolynomial.isHomogeneous_X A j') (by norm_num)).hom
            (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin n) A)
              (MvPolynomial.isHomogeneous_X A j') k g (by simpa using hg))) = 0) ∧
      z = HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin n) A)
            (MvPolynomial.isHomogeneous_X A j) k g (by simpa using hg) := by
  -- (I) the hypothesis, as a membership in the ideal of the `j`-th chart
  have hzI : (CommRingCat.Hom.hom (Proj.basicOpenIsoAway (StdGrading A n) (MvPolynomial.X j)
        (isHomogeneous_X_mem A n j) (by norm_num)).hom) z ∈
      i.ker.ideal ⟨Proj.basicOpen (StdGrading A n) (MvPolynomial.X j),
        Proj.isAffineOpen_basicOpen (StdGrading A n) (MvPolynomial.X j)
          (isHomogeneous_X_mem A n j) (by norm_num)⟩ :=
    (Ideal.Quotient.eq_zero_iff_mem).mp hz
  -- (II) write `z` as a fraction
  obtain ⟨k₀, a, ha, hzeq⟩ :=
    HomogeneousLocalization.Away.mk_surjective (StdGrading A n) (isHomogeneous_X_mem A n j) z
  -- (III) for every chart there is an exponent
  have hmain : ∀ j' : Fin n, ∃ m : ℕ,
      Away.mk (StdGrading A n) (f := MvPolynomial.X j') (d := 1)
          (isHomogeneous_X_mem A n j') (k₀ + m) (a * (MvPolynomial.X j) ^ m)
          (mem_add_smul_pow (isHomogeneous_X_mem A n j) ha m) ∈
        (i.ker.ideal ⟨Proj.basicOpen (StdGrading A n) (MvPolynomial.X j'),
          Proj.isAffineOpen_basicOpen (StdGrading A n) (MvPolynomial.X j')
            (isHomogeneous_X_mem A n j') (by norm_num)⟩).comap
          (CommRingCat.Hom.hom (Proj.basicOpenIsoAway (StdGrading A n) (MvPolynomial.X j')
            (isHomogeneous_X_mem A n j') (by norm_num)).hom) := by
    intro j'
    have hP : MvPolynomial.X j ∈ StdGrading A n 1 := MvPolynomial.isHomogeneous_X A j
    have hQ : MvPolynomial.X j' ∈ StdGrading A n 1 := MvPolynomial.isHomogeneous_X A j'
    have hx : (MvPolynomial.X j : MvPolynomial (Fin n) A) * MvPolynomial.X j' =
        MvPolynomial.X j' * MvPolynomial.X j := by
      ring
    have h2 : MvPolynomial.X j * MvPolynomial.X j' ∈ StdGrading A n 2 := by
      simpa using SetLike.mul_mem_graded hP hQ
    have hlt : (MvPolynomial.X j : MvPolynomial (Fin n) A) * MvPolynomial.X j' =
        (MvPolynomial.X j : MvPolynomial (Fin n) A) * MvPolynomial.X j' := rfl
    have htrans := chart_transport (𝒜 := StdGrading A n) (i := i) hP hQ
    have hzmap : (awayMap (StdGrading A n) hQ hlt) z ∈
        (((i.ker.ideal ⟨Proj.basicOpen (StdGrading A n) (MvPolynomial.X j'),
          Proj.isAffineOpen_basicOpen (StdGrading A n) (MvPolynomial.X j') hQ (by norm_num)⟩).comap
          (CommRingCat.Hom.hom (Proj.basicOpenIsoAway (StdGrading A n) (MvPolynomial.X j')
            hQ (by norm_num)).hom)).map
        (awayMap (StdGrading A n) hP hx)) := by
      have h1 : (awayMap (StdGrading A n) hQ hlt) z ∈
          (((i.ker.ideal ⟨Proj.basicOpen (StdGrading A n) (MvPolynomial.X j),
            Proj.isAffineOpen_basicOpen (StdGrading A n) (MvPolynomial.X j) hP (by norm_num)⟩).comap
            (CommRingCat.Hom.hom (Proj.basicOpenIsoAway (StdGrading A n) (MvPolynomial.X j)
              hP (by norm_num)).hom)).map
          (awayMap (StdGrading A n) hQ hlt)) :=
        Ideal.mem_map_of_mem _ (Ideal.mem_comap.mpr hzI)
      rwa [htrans] at h1
    -- the identity `am'(V₀) = u * am(z)`
    have hswap := away_mk_swap (𝒜 := StdGrading A n) (X := MvPolynomial.X j)
      (Y := MvPolynomial.X j') hP hQ k₀ a ha
    have hV0 : (awayMap (StdGrading A n) hP hx)
          (Away.mk (StdGrading A n) (f := MvPolynomial.X j') (d := 1) hQ k₀ a ha) =
        Away.mk (StdGrading A n) (f := MvPolynomial.X j * MvPolynomial.X j') (d := 2) h2 k₀
          (a * (MvPolynomial.X j) ^ k₀)
          (by simpa [smul_eq_mul, Nat.mul_two] using
            SetLike.mul_mem_graded ha (SetLike.pow_mem_graded k₀ hP)) := by
      rw [awayMap_mk]
    have hz' : z = Away.mk (StdGrading A n) (f := MvPolynomial.X j) (d := 1)
        (isHomogeneous_X_mem A n j) k₀ a ha := hzeq.symm
    have hzz : (awayMap (StdGrading A n) hQ hlt) z =
        Away.mk (StdGrading A n) (f := MvPolynomial.X j * MvPolynomial.X j') (d := 2) h2 k₀
          (a * (MvPolynomial.X j') ^ k₀)
          (by simpa [smul_eq_mul, Nat.mul_two] using
            SetLike.mul_mem_graded ha (SetLike.pow_mem_graded k₀ hQ)) := by
      rw [hz', awayMap_mk]
    have hmem2 : (awayMap (StdGrading A n) hP hx) (Away.mk (StdGrading A n)
          (f := MvPolynomial.X j') (d := 1) hQ k₀ a ha) ∈
        (((i.ker.ideal ⟨Proj.basicOpen (StdGrading A n) (MvPolynomial.X j'),
          Proj.isAffineOpen_basicOpen (StdGrading A n) (MvPolynomial.X j') hQ (by norm_num)⟩).comap
          (CommRingCat.Hom.hom (Proj.basicOpenIsoAway (StdGrading A n) (MvPolynomial.X j')
            hQ (by norm_num)).hom)).map
        (awayMap (StdGrading A n) hP hx)) := by
      rw [hV0, hswap]
      refine Ideal.mul_mem_left _ _ ?_
      rwa [hzz] at hzmap
    -- the localisation step
    letI : Algebra (Away (StdGrading A n) (MvPolynomial.X j'))
        (Away (StdGrading A n) (MvPolynomial.X j * MvPolynomial.X j')) :=
      (awayMap (StdGrading A n) hP hx).toAlgebra
    haveI : IsLocalization.Away (Away.isLocalizationElem hQ hP)
        (Away (StdGrading A n) (MvPolynomial.X j * MvPolynomial.X j')) :=
      Away.isLocalization_mul (hf := hQ) (hg := hP) (hx := hx) (hd := by norm_num)
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_of_algebraMap_mem_map
      (R := Away (StdGrading A n) (MvPolynomial.X j'))
      (S' := Away (StdGrading A n) (MvPolynomial.X j * MvPolynomial.X j'))
      (Away.isLocalizationElem hQ hP)
      (I := (i.ker.ideal ⟨Proj.basicOpen (StdGrading A n) (MvPolynomial.X j'),
        Proj.isAffineOpen_basicOpen (StdGrading A n) (MvPolynomial.X j') hQ (by norm_num)⟩).comap
        (CommRingCat.Hom.hom (Proj.basicOpenIsoAway (StdGrading A n) (MvPolynomial.X j')
          hQ (by norm_num)).hom))
      (v := Away.mk (StdGrading A n) (f := MvPolynomial.X j') (d := 1) hQ k₀ a ha) hmem2
    refine ⟨m, ?_⟩
    have ht : Away.isLocalizationElem hQ hP =
        Away.mk (StdGrading A n) (f := MvPolynomial.X j') (d := 1) hQ 1 ((MvPolynomial.X j) ^ 1)
          (by simpa using hP) := rfl
    have hfin : (Away.isLocalizationElem hQ hP) ^ m *
          Away.mk (StdGrading A n) (f := MvPolynomial.X j') (d := 1) hQ k₀ a ha =
        Away.mk (StdGrading A n) (f := MvPolynomial.X j') (d := 1) hQ (k₀ + m)
          (a * (MvPolynomial.X j) ^ m)
          (mem_add_smul_pow hP ha m) := by
      conv_lhs => rw [mul_comm]
      rw [ht, away_mk_pow (𝒜 := StdGrading A n) (f := MvPolynomial.X j') (d := 1) hQ hP m,
          away_mk_mul (𝒜 := StdGrading A n) (f := MvPolynomial.X j') (d := 1) hQ k₀ m a
            ((MvPolynomial.X j) ^ m) ha (SetLike.pow_mem_graded m hP)]
    rw [← hfin]
    exact hm
  choose m hm using hmain
  let M := Finset.univ.sup m
  refine ⟨k₀ + M, a * (MvPolynomial.X j) ^ M, ?_, ?_, ?_⟩
  · simpa using mem_add_smul_pow (isHomogeneous_X_mem A n j) ha M
  · intro j'
    refine (Ideal.Quotient.eq_zero_iff_mem).mpr ?_
    rw [← Ideal.mem_comap]
    have hmle : m j' ≤ M := by
      show m j' ≤ Finset.univ.sup m
      exact Finset.le_sup (Finset.mem_univ j')
    have hpad : Away.mk (StdGrading A n) (f := MvPolynomial.X j') (d := 1)
          (isHomogeneous_X_mem A n j') (k₀ + M) (a * (MvPolynomial.X j) ^ M)
          (mem_add_smul_pow (isHomogeneous_X_mem A n j) ha M) =
        Away.mk (StdGrading A n) (f := MvPolynomial.X j') (d := 1)
            (isHomogeneous_X_mem A n j') (k₀ + m j') (a * (MvPolynomial.X j) ^ (m j'))
            (mem_add_smul_pow (isHomogeneous_X_mem A n j) ha (m j')) *
          (Away.mk (StdGrading A n) (f := MvPolynomial.X j') (d := 1)
            (isHomogeneous_X_mem A n j') 1 ((MvPolynomial.X j) ^ 1)
            (by simpa using isHomogeneous_X_mem A n j)) ^ (M - m j') := by
      rw [away_mk_mul_pow (𝒜 := StdGrading A n) (f := MvPolynomial.X j') (d := 1)
        (isHomogeneous_X_mem A n j') (isHomogeneous_X_mem A n j)
        (k₀ + m j') (M - m j') (a * (MvPolynomial.X j) ^ (m j')) _]
      exact away_mk_congr (isHomogeneous_X_mem A n j') (by omega)
        (by rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hmle]) _ _
    rw [hpad]
    exact Ideal.mul_mem_right _ _ (hm j')
  · exact hzeq.symm.trans (away_mk_pad (𝒜 := StdGrading A n) (f := MvPolynomial.X j) (d := 1)
      (isHomogeneous_X_mem A n j) k₀ M a ha)

end Work.DSEQP
