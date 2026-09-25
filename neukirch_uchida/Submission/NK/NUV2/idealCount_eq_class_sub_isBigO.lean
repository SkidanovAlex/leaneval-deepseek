import Mathlib
import Submission.NK.HeckeL.Basic
import Submission.NK.NUV2.Minkowski.frontier_thickening_expMapBasis_paramSet
import Submission.NK.NUV2.Minkowski.frontier_thickening_normLeOne
import Submission.NK.NUV2.Geom.latticeCosetCount_sub_volume_isBigO

namespace NK.NUV2

open scoped nonZeroDivisors Classical Pointwise
open NumberField Ideal MeasureTheory MeasureTheory.Measure
open NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone

variable {K : Type*} [Field K] [NumberField K]

/-- **Exact identity: the count of ideals in a class equals the count of lattice points of the
corresponding ideal lattice in the fundamental cone.**

For an integral ideal `J` with `mk0 J = C⁻¹`, the nonzero integral ideals of class `C` and norm
`≤ s` are in bijection with the elements of the lattice `idealLattice K J` lying in the
fundamental cone and of norm `≤ s * absNorm J`, up to the `torsionOrder K` torsion units. -/
lemma classCount_eq_latticeCount (C : ClassGroup (𝓞 K)) (J : (Ideal (𝓞 K))⁰)
    (hJ : ClassGroup.mk0 J = C⁻¹) (s : ℝ) :
    (Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C} : ℝ)
        * (Units.torsionOrder K : ℝ)
      = (Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤
            s * (absNorm (J : Ideal (𝓞 K)) : ℝ)} : ℝ) := by
  classical
  have key : Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s ∧
        ClassGroup.mk0 I = C}
      = Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧
          Submodule.IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) ≤ s * absNorm (J : Ideal (𝓞 K))} := by
    simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
    refine Nat.card_congr ?_
    refine ((Equiv.dvd J).subtypeEquiv fun I ↦ ?_).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 K))⁰ ↦ J ∣ I) _)
    rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem _)]
    simp_rw [Equiv.dvd_apply, Submonoid.coe_mul, ← Submonoid.mul_def, _root_.map_mul, hJ,
      inv_mul_eq_one, Nat.cast_mul, mul_comm s, eq_comm, and_comm, and_congr_left_iff]
    exact fun _ ↦
      (mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors J))).symm
  rw [key]
  exact_mod_cast card_isPrincipal_dvd_norm_le K J
    (s * (absNorm (J : Ideal (𝓞 K)) : ℝ))

/-- The dilate of `normLeOne K` by `T ^ (1 / [K : ℚ])` is the intersection of the fundamental
cone with the norm ball of radius `T`. -/
lemma smul_normLeOne_eq (T : ℝ) (hT : 0 < T) :
    (T ^ ((Module.finrank ℚ K : ℝ)⁻¹)) • normLeOne K
      = fundamentalCone K ∩ {x : mixedSpace K | mixedEmbedding.norm x ≤ T} := by
  have hc : (0 : ℝ) < T ^ ((Module.finrank ℚ K : ℝ)⁻¹) := Real.rpow_pos_of_pos hT _
  have hcN : (T ^ ((Module.finrank ℚ K : ℝ)⁻¹)) ^ Module.finrank ℚ K = T :=
    Real.rpow_inv_natCast_pow hT.le Module.finrank_pos.ne'
  have hpos : (0 : ℝ) < (T ^ ((Module.finrank ℚ K : ℝ)⁻¹)) ^ Module.finrank ℚ K := by
    rw [hcN]; exact hT
  have key : ∀ y : ℝ,
      (T ^ ((Module.finrank ℚ K : ℝ)⁻¹))⁻¹ ^ Module.finrank ℚ K * y ≤ 1 ↔ y ≤ T := by
    intro y
    rw [inv_pow, inv_mul_le_iff₀ hpos, mul_one, hcN]
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne', mem_normLeOne,
    smul_mem_iff_mem (inv_ne_zero hc.ne'), mixedEmbedding.norm_smul, abs_inv, abs_of_pos hc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (key _).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (key _).mpr h2⟩

/-- The identity map between the `idealSet`-count and the lattice-point count in the corresponding
dilate of the fundamental cone. -/
noncomputable def idealSetEquivLatticeSubtype (J : (Ideal (𝓞 K))⁰) {T : ℝ} (hT : 0 < T) :
    {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ T} ≃
      {x : idealLattice K (FractionalIdeal.mk0 K J) //
        (x : mixedSpace K) ∈ (T ^ ((Module.finrank ℚ K : ℝ)⁻¹)) • normLeOne K} where
  toFun a := ⟨⟨(a.1 : mixedSpace K), by
      have ha : (a.1 : mixedSpace K) ∈
          (fundamentalCone K ∩ ↑(idealLattice K (FractionalIdeal.mk0 K J)) :
            Set (mixedSpace K)) := by
        simpa only [idealSet] using a.1.2
      exact ha.2⟩, by
    rw [smul_normLeOne_eq T hT]
    have ha : (a.1 : mixedSpace K) ∈
        (fundamentalCone K ∩ ↑(idealLattice K (FractionalIdeal.mk0 K J)) :
          Set (mixedSpace K)) := by
      simpa only [idealSet] using a.1.2
    exact ⟨ha.1, a.2⟩⟩
  invFun x := ⟨⟨(x.1 : mixedSpace K), by
      have hx : (x.1 : mixedSpace K) ∈
          fundamentalCone K ∩ {y : mixedSpace K | mixedEmbedding.norm y ≤ T} := by
        rw [← smul_normLeOne_eq T hT]
        exact x.2
      have hx' := hx
      rw [Set.mem_inter_iff] at hx'
      refine show (x.1 : mixedSpace K) ∈ idealSet K J from ?_
      rw [idealSet]
      exact ⟨hx'.1, x.1.2⟩⟩, by
    have hx : (x.1 : mixedSpace K) ∈
        fundamentalCone K ∩ {y : mixedSpace K | mixedEmbedding.norm y ≤ T} := by
      rw [← smul_normLeOne_eq T hT]
      exact x.2
    have hx' := hx
    rw [Set.mem_inter_iff] at hx'
    exact hx'.2⟩
  left_inv a := rfl
  right_inv x := rfl

lemma idealSet_card_eq_latticeCard (J : (Ideal (𝓞 K))⁰) {T : ℝ} (hT : 0 < T) :
    Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ T}
      = Nat.card {x : idealLattice K (FractionalIdeal.mk0 K J) //
          (x : mixedSpace K) ∈ (T ^ ((Module.finrank ℚ K : ℝ)⁻¹)) • normLeOne K} :=
  Nat.card_congr (idealSetEquivLatticeSubtype J hT)

/-- **The class count as a lattice point count.** -/
lemma classCount_eq_latticeCard_normLeOne (C : ClassGroup (𝓞 K)) (J : (Ideal (𝓞 K))⁰)
    (hJ : ClassGroup.mk0 J = C⁻¹) (T : ℝ) (hT : 0 < T) :
    (Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ T ∧ ClassGroup.mk0 I = C} : ℝ)
        * (Units.torsionOrder K : ℝ)
      = (Nat.card {x : idealLattice K (FractionalIdeal.mk0 K J) //
          (x : mixedSpace K) ∈
            ((T * (absNorm (J : Ideal (𝓞 K)) : ℝ)) ^
              ((Module.finrank ℚ K : ℝ)⁻¹)) • normLeOne K} : ℝ) := by
  rw [classCount_eq_latticeCount C J hJ T]
  exact_mod_cast idealSet_card_eq_latticeCard J
    (mul_pos hT (Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors J)))

/-- The constant `2^{-r₂} √|d_K|`, i.e. `covolume (idealLattice K J) / absNorm J`. -/
noncomputable def kappa (K : Type*) [Field K] [NumberField K] : ℝ :=
  2⁻¹ ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(NumberField.discr K : ℝ)|

omit [NumberField K] in
lemma kappa_pos (K : Type*) [Field K] [NumberField K] : 0 < kappa K := by
  refine mul_pos (pow_pos (by norm_num) _) (Real.sqrt_pos.mpr ?_)
  rw [abs_pos]
  exact_mod_cast NumberField.discr_ne_zero K

omit [NumberField K] in
lemma kappa_ne_zero (K : Type*) [Field K] [NumberField K] : kappa K ≠ 0 :=
  (kappa_pos K).ne'

/-- The covolume of the ideal lattice of `J` is `absNorm J · 2^{-r₂} √|d_K|`. -/
lemma covolume_idealLattice_eq (J : (Ideal (𝓞 K))⁰) :
    ZLattice.covolume (idealLattice K (FractionalIdeal.mk0 K J)) =
      (absNorm (J : Ideal (𝓞 K)) : ℝ) * kappa K := by
  rw [covolume_idealLattice, kappa, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm]
  ac_rfl

/-- The volume of the dilate of `normLeOne K`. -/
lemma volume_smul_normLeOne {t : ℝ} (ht : 0 < t) :
    (volume (t • normLeOne K)).toReal =
      t ^ (Module.finrank ℚ K : ℝ) * (volume (normLeOne K)).toReal := by
  rw [Measure.addHaar_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_pos (pow_pos ht _), Real.rpow_natCast, mixedEmbedding.finrank]

/-- The exponent computation `(x^{1/N})^{N-1} = x^{1-1/N}`. -/
lemma rpow_inv_pow_sub_one {x : ℝ} (hx : 0 < x) :
    (x ^ ((Module.finrank ℚ K : ℝ)⁻¹)) ^ ((Module.finrank ℚ K : ℝ) - 1)
      = x ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) := by
  rw [← Real.rpow_mul hx.le]
  congr 1
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  field_simp

/-- **Assembly.** Given the quantitative lattice point count for the ideal lattices of `K` (in the
region `normLeOne K`), the counts of ideals in two classes of the class group differ by
`O (X ^ (1 - 1/[K:ℚ]))`. -/
theorem idealCount_eq_class_sub_isBigO_of_latticeCount
    (hA : ∀ (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L],
      ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
        |((Nat.card {x : L // (x : mixedSpace K) ∈ t • normLeOne K} : ℝ) -
            (volume (t • normLeOne K)).toReal / ZLattice.covolume L)|
          ≤ C * t ^ ((Module.finrank ℝ (mixedSpace K) : ℝ) - (1 : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ C₁ C₂ : ClassGroup (𝓞 K),
      |((Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ X ∧ ClassGroup.mk0 I = C₁} : ℝ) -
        (Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ X ∧ ClassGroup.mk0 I = C₂} : ℝ))|
      ≤ C * X ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) := by
  classical
  haveI : Nonempty (ClassGroup (𝓞 K)) := ⟨1⟩
  have hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hnne : ((Module.finrank ℚ K : ℝ)) ≠ 0 := hn.ne'
  have hs : 0 ≤ 1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ) := by
    have h1 : (1 : ℝ) / (Module.finrank ℚ K : ℝ) ≤ 1 := by
      rw [div_le_one hn]; exact_mod_cast Module.finrank_pos
    linarith
  set w : ℝ := (Units.torsionOrder K : ℝ) with hwdef
  have hwpos : 0 < w := by rw [hwdef]; exact_mod_cast Units.torsionOrder_pos K
  let Jf : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰ :=
    fun C => Classical.choose (ClassGroup.mk0_surjective C⁻¹)
  have hJf : ∀ C, ClassGroup.mk0 (Jf C) = C⁻¹ :=
    fun C => Classical.choose_spec (ClassGroup.mk0_surjective C⁻¹)
  let Lt : ClassGroup (𝓞 K) → Submodule ℤ (mixedSpace K) :=
    fun C => idealLattice K (FractionalIdeal.mk0 K (Jf C))
  let Lc : ClassGroup (𝓞 K) → ℝ → ℕ :=
    fun C t => Nat.card {x : Lt C // (x : mixedSpace K) ∈ t • normLeOne K}
  -- the lattice point count for each class
  have hK : ∀ C : ClassGroup (𝓞 K), ∃ K' : ℝ, 0 < K' ∧ ∀ t : ℝ, 1 ≤ t →
      |((Lc C t : ℝ) - (volume (t • normLeOne K)).toReal / ZLattice.covolume (Lt C))|
        ≤ K' * t ^ ((Module.finrank ℝ (mixedSpace K) : ℝ) - (1 : ℝ)) :=
    fun C => hA (Lt C)
  let Kc : ClassGroup (𝓞 K) → ℝ := fun C => Classical.choose (hK C)
  have hKc_pos : ∀ C, 0 < Kc C := fun C => (Classical.choose_spec (hK C)).1
  have hKc_bd : ∀ C (t : ℝ), 1 ≤ t →
      |((Lc C t : ℝ) - (volume (t • normLeOne K)).toReal / ZLattice.covolume (Lt C))|
        ≤ Kc C * t ^ ((Module.finrank ℝ (mixedSpace K) : ℝ) - (1 : ℝ)) :=
    fun C => (Classical.choose_spec (hK C)).2
  have hne : (Finset.univ : Finset (ClassGroup (𝓞 K))).Nonempty := Finset.univ_nonempty
  set Kmax : ℝ := (Finset.univ : Finset (ClassGroup (𝓞 K))).sup' hne Kc with hKmaxdef
  have hKmax_pos : 0 < Kmax := by
    rw [hKmaxdef]
    exact lt_of_lt_of_le (hKc_pos 1) (Finset.le_sup' Kc (Finset.mem_univ 1))
  have hKc_le : ∀ C, Kc C ≤ Kmax := by
    intro C
    rw [hKmaxdef]
    exact Finset.le_sup' Kc (Finset.mem_univ C)
  set M : ℝ := (Finset.univ : Finset (ClassGroup (𝓞 K))).sup' hne
    (fun C => (Ideal.absNorm ((Jf C : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ)) with hMdef
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    refine le_trans ?_ (Finset.le_sup'
      (fun C' => (Ideal.absNorm ((Jf C' : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ))
      (Finset.mem_univ 1))
    exact_mod_cast (show (1 : ℕ) ≤ Ideal.absNorm ((Jf 1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) from
      absNorm_pos_of_nonZeroDivisors (Jf 1))
  have hNJ_le : ∀ C, (Ideal.absNorm ((Jf C : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ≤ M := by
    intro C
    rw [hMdef]
    exact Finset.le_sup'
      (fun C' => (Ideal.absNorm ((Jf C' : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ))
      (Finset.mem_univ C)
  have hNJ_pos : ∀ C, (0 : ℝ) < (absNorm ((Jf C : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) :=
    fun C => Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors (Jf C))
  have hNJ_one : ∀ C, (1 : ℝ) ≤ (absNorm ((Jf C : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) :=
    fun C => by
      have h : (1 : ℕ) ≤ Ideal.absNorm ((Jf C : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) :=
        absNorm_pos_of_nonZeroDivisors (Jf C)
      exact_mod_cast h
  refine ⟨2 * Kmax * M ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) / w, by positivity, ?_⟩
  intro X hX C₁ C₂
  let Sx : ClassGroup (𝓞 K) → ℕ := fun C =>
    Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ X ∧ ClassGroup.mk0 I = C}
  change |((Sx C₁ : ℝ) - (Sx C₂ : ℝ))|
      ≤ 2 * Kmax * M ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) / w *
          X ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ))
  have hconv : ∀ C : ClassGroup (𝓞 K), (Sx C : ℝ) * w =
      (Lc C ((X * (absNorm ((Jf C : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ)) ^
        ((Module.finrank ℚ K : ℝ)⁻¹)) : ℝ) := by
    intro C
    rw [hwdef]
    exact classCount_eq_latticeCard_normLeOne C (Jf C) (hJf C) X
      (lt_of_lt_of_le zero_lt_one hX)
  have hper : ∀ C : ClassGroup (𝓞 K),
      |(Sx C : ℝ) * w - X * (volume (normLeOne K)).toReal / kappa K|
        ≤ Kc C * (X * M) ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) := by
    intro C
    rw [hconv C]
    set T : ℝ := X * (absNorm ((Jf C : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) with hTdef
    have hTpos : 0 < T := mul_pos (lt_of_lt_of_le zero_lt_one hX) (hNJ_pos C)
    set t : ℝ := T ^ ((Module.finrank ℚ K : ℝ)⁻¹) with htdef
    have htpos : 0 < t := by rw [htdef]; exact Real.rpow_pos_of_pos hTpos _
    have ht1 : 1 ≤ t := by
      rw [htdef]
      refine Real.one_le_rpow ?_ (inv_nonneg.mpr hn.le)
      rw [hTdef]
      exact one_le_mul_of_one_le_of_one_le hX (hNJ_one C)
    have hvol : (volume (t • normLeOne K)).toReal = T * (volume (normLeOne K)).toReal := by
      rw [volume_smul_normLeOne htpos, htdef, Real.rpow_natCast,
        Real.rpow_inv_natCast_pow hTpos.le (Module.finrank_pos.ne')]
    have hmain : (volume (t • normLeOne K)).toReal / ZLattice.covolume (Lt C)
        = X * (volume (normLeOne K)).toReal / kappa K := by
      rw [hvol, covolume_idealLattice_eq, hTdef]
      have hk := kappa_ne_zero K
      have hJne : (absNorm ((Jf C : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ≠ 0 :=
        ne_of_gt (hNJ_pos C)
      field_simp
    have hrpow : t ^ ((Module.finrank ℝ (mixedSpace K) : ℝ) - (1 : ℝ))
        ≤ (X * M) ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) := by
      rw [mixedEmbedding.finrank, htdef, rpow_inv_pow_sub_one hTpos]
      refine Real.rpow_le_rpow (le_of_lt hTpos) ?_ hs
      rw [hTdef]
      exact mul_le_mul_of_nonneg_left (hNJ_le C) (le_of_lt (lt_of_lt_of_le zero_lt_one hX))
    have h1 : |(Lc C t : ℝ) - X * (volume (normLeOne K)).toReal / kappa K|
        ≤ Kc C * t ^ ((Module.finrank ℝ (mixedSpace K) : ℝ) - (1 : ℝ)) := by
      rw [← hmain]
      exact hKc_bd C t ht1
    exact le_trans h1 (mul_le_mul_of_nonneg_left hrpow (le_of_lt (hKc_pos C)))
  have hm : |(Sx C₁ : ℝ) * w - (Sx C₂ : ℝ) * w|
      ≤ 2 * Kmax * (X * M) ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) := by
    have hnn : 0 ≤ (X * M) ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) :=
      Real.rpow_nonneg (le_of_lt (mul_pos (lt_of_lt_of_le zero_lt_one hX)
        (lt_of_lt_of_le zero_lt_one hM1))) _
    have hle₁ := le_trans (hper C₁) (mul_le_mul_of_nonneg_right (hKc_le C₁) hnn)
    have hle₂ := le_trans (hper C₂) (mul_le_mul_of_nonneg_right (hKc_le C₂) hnn)
    have h3 := abs_sub_le ((Sx C₁ : ℝ) * w) (X * (volume (normLeOne K)).toReal / kappa K)
      ((Sx C₂ : ℝ) * w)
    rw [abs_sub_comm (X * (volume (normLeOne K)).toReal / kappa K)] at h3
    calc |(Sx C₁ : ℝ) * w - (Sx C₂ : ℝ) * w|
        ≤ |(Sx C₁ : ℝ) * w - X * (volume (normLeOne K)).toReal / kappa K|
          + |(Sx C₂ : ℝ) * w - X * (volume (normLeOne K)).toReal / kappa K| := h3
      _ ≤ Kmax * (X * M) ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ))
          + Kmax * (X * M) ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) := add_le_add hle₁ hle₂
      _ = 2 * Kmax * (X * M) ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) := by ring

  have hfinal : |(Sx C₁ : ℝ) - (Sx C₂ : ℝ)| * w
      ≤ 2 * Kmax * (X * M) ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) := by
    have hthis : ((Sx C₁ : ℝ) - (Sx C₂ : ℝ)) * w
        = (Sx C₁ : ℝ) * w - (Sx C₂ : ℝ) * w := by ring
    rw [← abs_of_pos hwpos, ← abs_mul, hthis]
    exact hm
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hkey : 2 * Kmax * (X * M) ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ))
      = (2 * Kmax * M ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) / w *
            X ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ))) * w := by
    rw [Real.mul_rpow (le_of_lt hXpos) (le_of_lt hMpos)]
    field_simp
  rw [hkey] at hfinal
  exact le_of_mul_le_mul_right hfinal hwpos

/-! ## The two analytic inputs, and the final theorem -/

/-- The Minkowski content bound for `frontier (normLeOne K)` in the form required by the lattice
point count: for `0 < ε ≤ 1` the `ε`-neighbourhood of the frontier has volume `≤ c ε`. -/
lemma cthickening_frontier_normLeOne_le (K : Type*) [Field K] [NumberField K] :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      volume (Metric.cthickening ε (frontier (normLeOne K))) ≤ ENNReal.ofReal (c * ε) := by
  obtain ⟨C, hCpos, hC⟩ := Minkowski.frontier_thickening_normLeOne_of_realSpace (K := K)
    (Minkowski.frontier_thickening_expMapBasis_paramSet K)
  refine ⟨C, hCpos, fun ε hε hε1 => ?_⟩
  have hset : Metric.cthickening ε (frontier (normLeOne K)) =
      {x : mixedSpace K | ∃ p ∈ frontier (normLeOne K), ‖x - p‖ ≤ ε} := by
    rw [Metric.cthickening_eq_biUnion_closedBall _ hε.le, isClosed_frontier.closure_eq]
    ext x
    constructor
    · intro hx
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
      exact ⟨p, hp, by simpa [dist_eq_norm] using Metric.mem_closedBall.mp hxp⟩
    · rintro ⟨p, hp, hxp⟩
      exact Set.mem_iUnion₂.mpr ⟨p, hp,
        Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hxp)⟩
  have hbdd : Bornology.IsBounded (frontier (normLeOne K)) :=
    (isBounded_normLeOne K).closure.subset frontier_subset_closure
  have hne : volume (Metric.cthickening ε (frontier (normLeOne K))) ≠ ⊤ :=
    ne_of_lt ((hbdd.cthickening).measure_lt_top (μ := volume))
  rw [ENNReal.le_ofReal_iff_toReal_le hne (by positivity), hset]
  exact hC ε hε hε1

/-- The quantitative lattice point count for a lattice in the mixed space, in the shape needed by
`idealCount_eq_class_sub_isBigO_of_latticeCount`. -/
lemma exists_latticeCount_bound (K : Type*) [Field K] [NumberField K] :
    ∀ (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L],
      ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
        |((Nat.card {x : L // (x : mixedSpace K) ∈ t • normLeOne K} : ℝ) -
            (volume (t • normLeOne K)).toReal / ZLattice.covolume L)|
          ≤ C * t ^ ((Module.finrank ℝ (mixedSpace K) : ℝ) - (1 : ℝ)) := by
  intro L _ _
  obtain ⟨C, hCpos, hC⟩ := Geom.latticeCosetCount_sub_volume_isBigO (mixedSpace K) L
    (normLeOne K) (isBounded_normLeOne K) (measurableSet_normLeOne K)
    (cthickening_frontier_normLeOne_le K) 0
  refine ⟨C, hCpos, fun t ht => ?_⟩
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set n : ℕ := Module.finrank ℝ (mixedSpace K) with hn
  set Y : ℝ := t ^ n with hY
  have hY1 : 1 ≤ Y := by rw [hY]; exact one_le_pow₀ ht
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY1
  have hpow : Y ^ ((Module.finrank ℝ (mixedSpace K) : ℝ)⁻¹) = t := by
    rw [hY, hn, ← Real.rpow_natCast, ← Real.rpow_mul htpos.le,
      mul_inv_cancel₀ (by
        have h : 0 < Module.finrank ℝ (mixedSpace K) := by
          rw [mixedEmbedding.finrank]; exact Module.finrank_pos
        exact_mod_cast h.ne'),
      Real.rpow_one]
  have hvol : Y * (volume (normLeOne K)).toReal = (volume (t • normLeOne K)).toReal := by
    rw [Measure.addHaar_smul_of_nonneg volume htpos.le, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg htpos.le _), hY, hn]
  have hexp : Y ^ (1 - (Module.finrank ℝ (mixedSpace K) : ℝ)⁻¹)
      = t ^ ((Module.finrank ℝ (mixedSpace K) : ℝ) - 1) := by
    rw [hY, hn, ← Real.rpow_natCast, ← Real.rpow_mul htpos.le]
    congr 1
    have hn0 : (Module.finrank ℝ (mixedSpace K) : ℝ) ≠ 0 := by
      have h : 0 < Module.finrank ℝ (mixedSpace K) := by
        rw [mixedEmbedding.finrank]; exact Module.finrank_pos
      exact_mod_cast h.ne'
    field_simp
  have hcard : Nat.card {x : L // (0 : mixedSpace K) + (x : mixedSpace K) ∈
        Y ^ ((Module.finrank ℝ (mixedSpace K) : ℝ)⁻¹) • normLeOne K}
      = Nat.card {x : L // (x : mixedSpace K) ∈ t • normLeOne K} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [hpow, zero_add]
  have hgoal := hC Y hY1
  rw [hcard, hvol, hexp] at hgoal
  exact hgoal

/-- **Geometric core, ideal-class-group form: the count of integral ideals of norm `≤ X` in a fixed
class is uniform in the class up to `O(X^{1-1/[K:ℚ]})`.**

This is the idèle-free instance (the `U` maximal, `S = ∅` case) of the analytic crux of the
requested `NK.NUV2.heckeL_regular_of_ne_one`, and it is the case closest to what Mathlib already
proves *without* an error term: `NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop` says that
for each class `C` the ratio `#{I : absNorm I ≤ X, mk0 I = C}/X` tends (as `X → ∞`) to the *same*
constant `2^{r₁}(2π)^{r₂}·Reg/(w·√|d|)`, independent of `C`.  The present statement asks for the
quantitative version: the difference of the counts of two classes is `O(X^{1-1/[K:ℚ]})`. -/
theorem idealCount_eq_class_sub_isBigO (K : Type) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      ∀ C₁ C₂ : ClassGroup (NumberField.RingOfIntegers K),
        |((Nat.card {I : (Ideal (NumberField.RingOfIntegers K))⁰ //
              Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) ≤ X ∧
              ClassGroup.mk0 I = C₁} : ℝ)
        - (Nat.card {I : (Ideal (NumberField.RingOfIntegers K))⁰ //
              Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) ≤ X ∧
              ClassGroup.mk0 I = C₂} : ℝ))|
      ≤ C * X ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) :=
  idealCount_eq_class_sub_isBigO_of_latticeCount (K := K) (exists_latticeCount_bound K)

end NK.NUV2
