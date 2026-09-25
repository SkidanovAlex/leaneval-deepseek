import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.FieldTheory.Galois.range_norm_le_range_norm_of_intermediateField
import Submission.Commons.FieldTheory.Galois.natCard_quotient_units_range_norm_le_mul_tower

namespace Commons.FieldTheory.Galois

open IntermediateField

/-- The `E/M`-norm of the image in `E` of a unit `a` of the intermediate field `M` is
`a ^ [E : M]`.  This is `Algebra.norm_algebraMap` transported to units. -/
theorem norm_unit_map_algebraMap {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (M : IntermediateField F E) (a : (↥M)ˣ) :
    Units.map (Algebra.norm ↥M : E →* ↥M) (Units.map (algebraMap ↥M E) a) =
      a ^ (Module.finrank ↥M E) := by
  apply Units.ext
  simp only [Units.coe_map, Units.val_pow_eq_pow_val]
  change (Algebra.norm ↥M) (algebraMap ↥M E (a : ↥M)) = (a : ↥M) ^ Module.finrank ↥M E
  rw [Algebra.norm_algebraMap]

/-- In a commutative group, an element whose `m`-th and `n`-th powers lie in a subgroup `A`
(with `m` and `n` coprime) already lies in `A`. -/
theorem mem_of_pow_mem_of_coprime {G : Type*} [CommGroup G] (A : Subgroup G) (x : G) {m n : ℕ}
    (hcop : Nat.Coprime m n) (hm : x ^ m ∈ A) (hn : x ^ n ∈ A) : x ∈ A := by
  have hkm : x ^ m ∈ MonoidHom.ker (QuotientGroup.mk' A) := by
    rw [QuotientGroup.ker_mk']; exact hm
  have hkn : x ^ n ∈ MonoidHom.ker (QuotientGroup.mk' A) := by
    rw [QuotientGroup.ker_mk']; exact hn
  have hq : QuotientGroup.mk' A x = 1 := by
    have ho1 : orderOf (QuotientGroup.mk' A x) ∣ m :=
      orderOf_dvd_iff_pow_eq_one.mpr (by
        rw [← map_pow (QuotientGroup.mk' A) x m]; exact MonoidHom.mem_ker.mp hkm)
    have ho2 : orderOf (QuotientGroup.mk' A x) ∣ n :=
      orderOf_dvd_iff_pow_eq_one.mpr (by
        rw [← map_pow (QuotientGroup.mk' A) x n]; exact MonoidHom.mem_ker.mp hkn)
    have ho : orderOf (QuotientGroup.mk' A x) = 1 :=
      Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd ho1 ho2)
    exact orderOf_eq_one_iff.mp ho
  have : x ∈ MonoidHom.ker (QuotientGroup.mk' A) := hq
  rwa [QuotientGroup.ker_mk'] at this

/-- For subgroups `H, K` of a group whose (finite) indices are coprime, the index of the
intersection is the product of the indices. -/
theorem index_inf_eq_mul_index_of_coprime {G : Type*} [Group G] (H K : Subgroup G)
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hH : H.index = m) (hK : K.index = n)
    (hcop : Nat.Coprime m n) : (H ⊓ K).index = m * n := by
  have hHne : H.index ≠ 0 := by rw [hH]; exact hm
  have hKne : K.index ≠ 0 := by rw [hK]; exact hn
  have hpos : 0 < (H ⊓ K).index := Nat.pos_of_ne_zero (Subgroup.index_inf_ne_zero hHne hKne)
  have hle : (H ⊓ K).index ≤ m * n := by
    have h := Subgroup.index_inf_le (H := H) (K := K)
    rwa [hH, hK] at h
  have hdvdm : m ∣ (H ⊓ K).index := by
    have h := Subgroup.relIndex_mul_index (H := H ⊓ K) (K := H) inf_le_left
    rw [hH] at h
    exact ⟨(H ⊓ K).relIndex H, by rw [mul_comm]; exact h.symm⟩
  have hdvdn : n ∣ (H ⊓ K).index := by
    have h := Subgroup.relIndex_mul_index (H := H ⊓ K) (K := K) inf_le_right
    rw [hK] at h
    exact ⟨(H ⊓ K).relIndex K, by rw [mul_comm]; exact h.symm⟩
  have hdvd : m * n ∣ (H ⊓ K).index := hcop.mul_dvd_of_dvd_of_dvd hdvdm hdvdn
  exact le_antisymm hle (Nat.le_of_dvd hpos hdvd)

/-- For coprime-degree intermediate fields `M`, `N` of a finite extension `E / F` with
`[E : F] = [M : F] * [N : F]`, the intersection of the unit-norm ranges of `M` and `N` lies
in the unit-norm range of `E`.

If `x = N_{M/F}(a) = N_{N/F}(b)` with `a ∈ Mˣ`, `b ∈ Nˣ`, then
`N_{E/F}(a) = x ^ [E : M]` and `N_{E/F}(b) = x ^ [E : N]`; since
`[E : M] = [N : F]` and `[E : N] = [M : F]` are coprime, `x` is a product of the two powers
and hence itself lies in the norm range of `E`. -/
theorem range_norm_inf_le_range_norm_of_coprime_finrank
    {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (M N : IntermediateField F E)
    (hcop : Nat.Coprime (Module.finrank F M) (Module.finrank F N))
    (hdeg : Module.finrank F E = Module.finrank F M * Module.finrank F N) :
    MonoidHom.range (Units.map (Algebra.norm F : ↥M →* F)) ⊓
      MonoidHom.range (Units.map (Algebra.norm F : ↥N →* F)) ≤
      MonoidHom.range (Units.map (Algebra.norm F : E →* F)) := by
  intro x hx
  rw [Subgroup.mem_inf, MonoidHom.mem_range, MonoidHom.mem_range] at hx
  obtain ⟨a, ha⟩ := hx.1
  obtain ⟨b, hb⟩ := hx.2
  have hm : 0 < Module.finrank F M := Module.finrank_pos
  have hn : 0 < Module.finrank F N := Module.finrank_pos
  have hdimME : Module.finrank ↥M E = Module.finrank F N := by
    have h := Module.finrank_mul_finrank F ↥M E
    rw [hdeg] at h
    exact Nat.mul_left_cancel hm h
  have hdimNE : Module.finrank ↥N E = Module.finrank F M := by
    have h := Module.finrank_mul_finrank F ↥N E
    rw [hdeg] at h
    exact Nat.mul_left_cancel hn (h.trans (mul_comm _ _))
  have hpowN : x ^ (Module.finrank F N) ∈
      MonoidHom.range (Units.map (Algebra.norm F : E →* F)) := by
    refine ⟨Units.map (algebraMap ↥M E) a, ?_⟩
    rw [← norm_unit_comp_norm_unit (F := F) (K := ↥M) (E := E),
        MonoidHom.comp_apply, norm_unit_map_algebraMap (M := M) (a := a), map_pow, ha,
        ← hdimME]
  have hpowM : x ^ (Module.finrank F M) ∈
      MonoidHom.range (Units.map (Algebra.norm F : E →* F)) := by
    refine ⟨Units.map (algebraMap ↥N E) b, ?_⟩
    rw [← norm_unit_comp_norm_unit (F := F) (K := ↥N) (E := E),
        MonoidHom.comp_apply, norm_unit_map_algebraMap (M := N) (a := b), map_pow, hb,
        ← hdimNE]
  exact mem_of_pow_mem_of_coprime _ x hcop hpowM hpowN

/-- **Norm index bound for a compositum of coprime-degree intermediate fields.**

Let `E / F` be a finite-dimensional field extension and `M, N` intermediate fields with
`M ⊔ N = ⊤`, `M ⊓ N = ⊥` and coprime degrees `[M : F]`, `[N : F]`.  Assume that for `M` and `N`
the norm index equals the degree:
`|Fˣ ⧸ N_{M/F}(Mˣ)| = [M : F]` and `|Fˣ ⧸ N_{N/F}(Nˣ)| = [N : F]`.
Then `[E : F] ≤ |Fˣ ⧸ N_{E/F}(Eˣ)|`.

Indeed `[E : F] = [M : F] · [N : F]` by coprimality, while by transitivity of the norm
`N_{E/F}(Eˣ) = N_{M/F}(Mˣ) ⊓ N_{N/F}(Nˣ)`; the two norm ranges have coprime indices, so the
index of their intersection — hence the cardinality of `Fˣ ⧸ N_{E/F}(Eˣ)` — is the product
`[M : F] · [N : F]`. -/
theorem le_finrank_of_coprime_intermediate
    {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (M N : IntermediateField F E)
    (hcop : Nat.Coprime (Module.finrank F M) (Module.finrank F N))
    (hMN : M ⊔ N = ⊤) (hdisj : M ⊓ N = ⊥)
    (hM : Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : ↥M →* F)))
      = Module.finrank F M)
    (hN : Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : ↥N →* F)))
      = Module.finrank F N) :
    Module.finrank F E ≤
      Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : E →* F))) := by
  -- `hdisj` (the triviality of `M ⊓ N`) is part of the hypothesis; coprimality already
  -- forces `M` and `N` to be linearly disjoint, so it is not needed for the proof.
  have _ : M ⊓ N = ⊥ := hdisj
  set NM : Subgroup Fˣ := MonoidHom.range (Units.map (Algebra.norm F : ↥M →* F)) with hNMdef
  set NN : Subgroup Fˣ := MonoidHom.range (Units.map (Algebra.norm F : ↥N →* F)) with hNNdef
  set NE : Subgroup Fˣ := MonoidHom.range (Units.map (Algebra.norm F : E →* F)) with hNEdef
  -- coprimality forces linear disjointness, hence `[E : F] = [M : F] * [N : F]`
  have hdeg : Module.finrank F E = Module.finrank F M * Module.finrank F N := by
    have hld : M.LinearDisjoint ↥N := LinearDisjoint.of_finrank_coprime hcop
    have h1 : Module.finrank F ↥(M ⊔ N) = Module.finrank F M * Module.finrank F N :=
      hld.finrank_sup
    rw [hMN, IntermediateField.finrank_top'] at h1
    exact h1
  -- the norm range of `E` is the intersection of the norm ranges of `M` and `N`
  have hkey : NE = NM ⊓ NN := by
    refine le_antisymm ?_ ?_
    · rw [hNEdef, hNMdef, hNNdef]
      exact le_inf (range_norm_le_range_norm_of_intermediateField M)
        (range_norm_le_range_norm_of_intermediateField N)
    · rw [hNEdef, hNMdef, hNNdef]
      exact range_norm_inf_le_range_norm_of_coprime_finrank M N hcop hdeg
  have hNMindex : NM.index = Module.finrank F M := by
    rw [Subgroup.index_eq_card]; exact hM
  have hNNindex : NN.index = Module.finrank F N := by
    rw [Subgroup.index_eq_card]; exact hN
  have hmne : Module.finrank F M ≠ 0 := (Module.finrank_pos).ne'
  have hnne : Module.finrank F N ≠ 0 := (Module.finrank_pos).ne'
  have hindex : NE.index = Module.finrank F E := by
    rw [hkey, index_inf_eq_mul_index_of_coprime NM NN hmne hnne hNMindex hNNindex hcop, ← hdeg]
  have hcard : Nat.card (Fˣ ⧸ NE) = Module.finrank F E := by
    rw [← Subgroup.index_eq_card NE]; exact hindex
  exact le_of_eq hcard.symm

end Commons.FieldTheory.Galois