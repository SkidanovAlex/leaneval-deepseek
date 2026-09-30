import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.subgroup_rayDegAux
import Submission.Work.BW.mat_vecMul_eq_zero
import Submission.Work.BW.natAbs_det_smul_mem_span
import Submission.Work.BW.exists_rep_mod
import Submission.Work.BW.boxPts_eq_Icc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace Work.BW
-- ==== definitions for the argument ====

noncomputable def projJ {N ρ : ℕ} (J : Finset (Fin N)) (hJ : J.card = ρ) :
    (Fin N → ℤ) →ₗ[ℤ] (Fin ρ → ℤ) :=
  LinearMap.pi (fun b : Fin ρ =>
    LinearMap.proj (R := ℤ) (φ := fun _ : Fin N => ℤ) (J.orderEmbOfFin hJ b))

lemma projJ_apply {N ρ : ℕ} (J : Finset (Fin N)) (hJ : J.card = ρ)
    (x : Fin N → ℤ) (b : Fin ρ) : projJ J hJ x b = x (J.orderEmbOfFin hJ b) := by
  simp [projJ]

noncomputable def jIdx {N ρ : ℕ} (J : Finset (Fin N)) (hJ : J.card = ρ) (i : Fin N)
    (h : i ∈ J) : Fin ρ :=
  (J.orderIsoOfFin hJ).symm ⟨i, h⟩

lemma orderEmbOfFin_jIdx {N ρ : ℕ} (J : Finset (Fin N)) (hJ : J.card = ρ) (i : Fin N)
    (h : i ∈ J) : J.orderEmbOfFin hJ (jIdx J hJ i h) = i := by
  unfold jIdx
  have h1 := Finset.coe_orderIsoOfFin_apply J hJ ((J.orderIsoOfFin hJ).symm ⟨i, h⟩)
  rw [OrderIso.apply_symm_apply] at h1
  simpa using h1.symm

noncomputable def pt {N ρ : ℕ} (J : Finset (Fin N)) (hJ : J.card = ρ) (r : Fin ρ → ℤ)
    (b : Fin N → ℤ) : Fin N → ℤ :=
  fun i => if h : i ∈ J then r (jIdx J hJ i h) else b i

lemma pt_projJ {N ρ : ℕ} (J : Finset (Fin N)) (hJ : J.card = ρ) (r : Fin ρ → ℤ)
    (b : Fin N → ℤ) : projJ J hJ (pt J hJ r b) = r := by
  funext b'
  rw [projJ_apply]
  simp only [pt]
  rw [dif_pos (J.orderEmbOfFin_mem hJ b')]
  congr 1
  exact (J.orderEmbOfFin hJ).injective (by rw [orderEmbOfFin_jIdx])

lemma pt_of_notMem {N ρ : ℕ} (J : Finset (Fin N)) (hJ : J.card = ρ) (r : Fin ρ → ℤ)
    (b : Fin N → ℤ) {i : Fin N} (hi : i ∉ J) : pt J hJ r b i = b i := by
  simp only [pt]
  rw [dif_neg hi]

end Work.BW

namespace Work.BW

/-- The quotient of `ℤ^ρ` by the `ℤ`-span of the rows of a *non-singular* integer matrix `A` has
exactly `|det A|` elements.  (Smith normal form / covolume: the rows form a `ℤ`-basis of their
span, and the determinant of that basis against the standard basis is `det A`.) -/
lemma nat_card_span_rows_ne {ρ : ℕ} (A : Matrix (Fin ρ) (Fin ρ) ℤ) (hA : A.det ≠ 0) :
    Nat.card ((Fin ρ → ℤ) ⧸ Submodule.span ℤ (Set.range (fun j => A j))) = A.det.natAbs := by
  classical
  have hli : LinearIndependent ℤ (fun j : Fin ρ => A j) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hceq : c = 0 := mat_vecMul_eq_zero A hA c (fun b => by
      have h := congrFun hc b
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h)
    exact congrFun hceq i
  let N : Submodule ℤ (Fin ρ → ℤ) := Submodule.span ℤ (Set.range (fun j => A j))
  let bN : Module.Basis (Fin ρ) ℤ ↥N := Module.Basis.span hli
  let b : Module.Basis (Fin ρ) ℤ (Fin ρ → ℤ) := Pi.basisFun ℤ (Fin ρ)
  have key : (b.det (Subtype.val ∘ ⇑bN)).natAbs = Nat.card ((Fin ρ → ℤ) ⧸ N) :=
    Submodule.natAbs_det_basis_change b N bN
  rw [← key]
  congr 1
  rw [Module.Basis.det_apply, ← Matrix.det_transpose A]
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr,
    Function.comp_apply, b, bN]
  exact congrFun (congrArg Subtype.val (Module.Basis.span_apply hli j)) i

/-- Lower bound for the number of classes of a box modulo a lattice: for an integer matrix `M : Fin ρ → Fin N → ℤ`, a box `∏ᵢ [0, mᵢ]` whose `J`-coordinates are large enough that the `J`-sub-box contains `{0,…,|Δ_J|-1}^J` (`|Δ_J| ≤ mⱼ + 1` for `j ∈ J`), and every `ρ`-set `J` of columns, `|Δ_J| · ∏_{i∉J}(mᵢ+1)` is at most the number of classes of the box modulo the lattice spanned by the rows of `M`. (For each of the `|Δ_J|` classes of `ℤ^J/L_J` pick a representative in the `J`-sub-box and translate the `Jᶜ`-sub-box: the translates are pairwise inequivalent, since `(u_J = 0 ∧ (0,u) ∈ L) ⟹ u = 0` when `det M|_J ≠ 0`.) -/
theorem boxClass_lower {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (m : Fin N → ℕ)
    (J : Finset (Fin N)) (hJ : J.card = ρ)
    (hbig : ∀ j ∈ J, (minorJ M J hJ).natAbs ≤ m j + 1) :
    |(minorJ M J hJ : ℚ)| * ∏ i ∈ Jᶜ, ((m i : ℚ) + 1) ≤ (boxClassCount N ρ M m : ℚ) := by
  classical
  set A : Matrix (Fin ρ) (Fin ρ) ℤ := fun a b => M a (J.orderEmbOfFin hJ b) with hAdef
  have hdetA : A.det = minorJ M J hJ := rfl
  set d : ℕ := A.det.natAbs with hddef
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · have hdet0 : A.det = 0 := by rw [hddef] at hd0; exact Int.natAbs_eq_zero.mp hd0
    have hminj : minorJ M J hJ = 0 := by rw [← hdetA, hdet0]
    rw [hminj]
    simp only [Int.cast_zero, abs_zero, zero_mul]
    exact Nat.cast_nonneg _
  · have hdet_ne : A.det ≠ 0 := by
      intro h0; rw [hddef, h0, Int.natAbs_zero] at hdpos; exact absurd hdpos (lt_irrefl 0)
    set L : Submodule ℤ (Fin ρ → ℤ) := Submodule.span ℤ (Set.range (fun j => A j)) with hLdef
    have hLcard : Nat.card ((Fin ρ → ℤ) ⧸ L) = d := by
      rw [hLdef, hddef]; exact nat_card_span_rows_ne A hdet_ne
    have hLmem : ∀ y : Fin ρ → ℤ, ((d : ℤ) • y) ∈ L := by
      intro y; rw [hLdef, hddef]; exact natAbs_det_smul_mem_span A y
    obtain ⟨rep, hrep_mk, hrep_lt⟩ := exists_rep_mod L d hdpos hLmem
    haveI : Finite ((Fin ρ → ℤ) ⧸ L) :=
      (Nat.card_ne_zero.mp (by rw [hLcard]; exact hdpos.ne')).2
    letI : Fintype ((Fin ρ → ℤ) ⧸ L) := Fintype.ofFinite _
    set Reps : Finset (Fin ρ → ℤ) := (Finset.univ : Finset ((Fin ρ → ℤ) ⧸ L)).image rep
      with hRepsdef
    have hReps_card : Reps.card = d := by
      have hinj : Set.InjOn rep ↑(Finset.univ : Finset ((Fin ρ → ℤ) ⧸ L)) := by
        intro c _ c' _ hcc
        have h1 := congrArg (fun z : Fin ρ → ℤ => (Submodule.Quotient.mk z : (Fin ρ → ℤ) ⧸ L)) hcc
        rw [hrep_mk, hrep_mk] at h1
        exact h1
      rw [hRepsdef, Finset.card_image_of_injOn hinj, Finset.card_univ,
        ← Nat.card_eq_fintype_card, hLcard]
    set boxJC : Finset (Fin N → ℤ) :=
      Fintype.piFinset (fun i : Fin N => (if i ∈ J then ({0} : Finset ℤ) else Finset.Icc 0 (m i)))
      with hboxJCdef
    have hboxJC_mem : ∀ b : Fin N → ℤ, b ∈ boxJC ↔
        (∀ i ∈ J, b i = 0) ∧ (∀ i ∉ J, 0 ≤ b i ∧ b i ≤ (m i : ℤ)) := by
      intro b
      rw [hboxJCdef, Fintype.mem_piFinset]
      constructor
      · intro h
        refine ⟨fun i hi => ?_, fun i hi => ?_⟩
        · have hh := h i; rw [if_pos hi, Finset.mem_singleton] at hh; exact hh
        · have hh := h i; rw [if_neg hi, Finset.mem_Icc] at hh; exact hh
      · rintro ⟨h1, h2⟩ i
        by_cases hi : i ∈ J
        · rw [if_pos hi, Finset.mem_singleton]; exact h1 i hi
        · rw [if_neg hi, Finset.mem_Icc]; exact h2 i hi
    have hboxJC_card : boxJC.card = ∏ i ∈ Jᶜ, (m i + 1) := by
      rw [hboxJCdef, Fintype.card_piFinset]
      have h1 : ∀ i : Fin N,
          ((if i ∈ J then ({0} : Finset ℤ) else Finset.Icc 0 (m i))).card =
            (if i ∈ J then 1 else (m i + 1)) := by
        intro i
        by_cases hi : i ∈ J
        · simp only [hi, if_true, Finset.card_singleton]
        · simp only [hi, if_false, Int.card_Icc]
          have h2 : (m i : ℤ) + 1 - 0 = ((m i + 1 : ℕ) : ℤ) := by push_cast; ring
          rw [h2, Int.toNat_natCast]
      trans ∏ i : Fin N, (if i ∈ J then 1 else (m i + 1))
      · exact Finset.prod_congr rfl (fun i _ => h1 i)
      · rw [Finset.prod_ite]
        simp only [Finset.prod_const_one, one_mul]
        congr 1
        ext x
        simp
    have hd_le : ∀ j ∈ J, (d : ℤ) ≤ (m j : ℤ) + 1 := by
      intro j hj
      have h1 : d ≤ m j + 1 := by rw [hddef, hdetA]; exact hbig j hj
      exact_mod_cast h1
    have hboxPts_mem : ∀ x : Fin N → ℤ, x ∈ boxPts N m ↔ ∀ i, 0 ≤ x i ∧ x i ≤ (m i : ℤ) := by
      intro x
      rw [boxPts_eq_Icc N m, Finset.mem_Icc, Pi.le_def]
      constructor
      · rintro ⟨h1, h2⟩ i; exact ⟨by simpa using h1 i, by simpa using h2 i⟩
      · intro h; exact ⟨fun i => (h i).1, fun i => (h i).2⟩
    have hmap : Submodule.map (projJ J hJ) (rowLat N ρ M) = L := by
      have hfun : (⇑(projJ J hJ) ∘ M) = (fun j : Fin ρ => A j) := by
        funext j b
        simp only [Function.comp_apply, hAdef, projJ_apply]
      rw [rowLat, hLdef, Submodule.map_span, ← Set.range_comp, hfun]
    have hker : ∀ z ∈ rowLat N ρ M, projJ J hJ z = 0 → z = 0 := by
      intro z hz hz0
      rw [rowLat, Submodule.mem_span_range_iff_exists_fun] at hz
      obtain ⟨c, hc⟩ := hz
      have h1 : projJ J hJ (∑ j, c j • M j) = 0 := by rw [hc]; exact hz0
      rw [map_sum] at h1
      have h2 : ∀ b, ∑ j, c j * A j b = 0 := by
        intro b
        have h3 := congrFun h1 b
        simpa [hAdef, projJ_apply, Finset.sum_apply] using h3
      have hc0 : c = 0 := mat_vecMul_eq_zero A hdet_ne c h2
      rw [← hc, hc0]
      simp
    have hMapsTo : Set.MapsTo
        (fun p : (Fin ρ → ℤ) × (Fin N → ℤ) =>
          (Submodule.Quotient.mk (pt J hJ p.1 p.2) : (Fin N → ℤ) ⧸ rowLat N ρ M))
        ↑(Reps ×ˢ boxJC)
        ↑((boxPts N m).image (fun b => (Submodule.Quotient.mk b : (Fin N → ℤ) ⧸ rowLat N ρ M))) := by
      rintro ⟨r, b⟩ hp
      simp only [Finset.mem_coe, Finset.mem_product] at hp
      obtain ⟨hr, hb⟩ := hp
      simp only [Finset.mem_coe, Finset.mem_image]
      refine ⟨pt J hJ r b, ?_, rfl⟩
      rw [hboxPts_mem]
      intro i
      constructor
      · by_cases hi : i ∈ J
        · rw [pt, dif_pos hi]
          obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
          exact (hrep_lt c _).1
        · rw [pt, dif_neg hi]
          exact ((hboxJC_mem b).mp hb).2 i hi |>.1
      · by_cases hi : i ∈ J
        · rw [pt, dif_pos hi]
          obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
          have h1 := (hrep_lt c (jIdx J hJ i hi)).2
          have h2 := hd_le i hi
          linarith
        · rw [pt, dif_neg hi]
          exact ((hboxJC_mem b).mp hb).2 i hi |>.2
    have hInj : Set.InjOn
        (fun p : (Fin ρ → ℤ) × (Fin N → ℤ) =>
          (Submodule.Quotient.mk (pt J hJ p.1 p.2) : (Fin N → ℤ) ⧸ rowLat N ρ M))
        ↑(Reps ×ˢ boxJC) := by
      rintro ⟨r, b⟩ hp ⟨r', b'⟩ hp' heq
      simp only [Finset.mem_coe, Finset.mem_product] at hp hp'
      obtain ⟨hr, hb⟩ := hp
      obtain ⟨hr', hb'⟩ := hp'
      obtain ⟨c, -, hcr⟩ := Finset.mem_image.mp hr
      obtain ⟨c', -, hc'r'⟩ := Finset.mem_image.mp hr'
      have hsub : pt J hJ r b - pt J hJ r' b' ∈ rowLat N ρ M :=
        (Submodule.Quotient.eq (rowLat N ρ M)).mp heq
      have hproj : projJ J hJ (pt J hJ r b - pt J hJ r' b') ∈ L := by
        rw [← hmap]
        exact Submodule.mem_map.mpr ⟨_, hsub, rfl⟩
      rw [map_sub, pt_projJ, pt_projJ] at hproj
      have hmk : (Submodule.Quotient.mk r : (Fin ρ → ℤ) ⧸ L) = Submodule.Quotient.mk r' :=
        (Submodule.Quotient.eq L).mpr hproj
      rw [← hcr, ← hc'r', hrep_mk, hrep_mk] at hmk
      have hrr' : r = r' := by rw [← hcr, ← hc'r', hmk]
      have hsub2 : pt J hJ r b - pt J hJ r b' ∈ rowLat N ρ M := by simpa [hrr'] using hsub
      have hker0 : projJ J hJ (pt J hJ r b - pt J hJ r b') = 0 := by
        rw [map_sub, pt_projJ, pt_projJ, sub_self]
      have hzero : pt J hJ r b - pt J hJ r b' = 0 := hker _ hsub2 hker0
      have hbb' : b = b' := by
        funext i
        by_cases hi : i ∈ J
        · rw [((hboxJC_mem b).mp hb).1 i hi, ((hboxJC_mem b').mp hb').1 i hi]
        · have hi' := congrFun hzero i
          rw [Pi.sub_apply, pt_of_notMem J hJ r b hi, pt_of_notMem J hJ r b' hi] at hi'
          exact sub_eq_zero.mp hi'
      rw [hrr', hbb']
    have hle := Finset.card_le_card_of_injOn
      (fun p : (Fin ρ → ℤ) × (Fin N → ℤ) =>
        (Submodule.Quotient.mk (pt J hJ p.1 p.2) : (Fin N → ℤ) ⧸ rowLat N ρ M))
      hMapsTo hInj
    rw [Finset.card_product, hReps_card, hboxJC_card] at hle
    have hcast : ((d * ∏ i ∈ Jᶜ, (m i + 1) : ℕ) : ℚ) ≤ (boxClassCount N ρ M m : ℚ) := by
      exact_mod_cast hle
    rw [Nat.cast_mul, Nat.cast_prod] at hcast
    push_cast at hcast
    have hdc : (d : ℚ) = |(minorJ M J hJ : ℚ)| := by
      rw [hddef, ← hdetA]
      calc ((A.det.natAbs : ℕ) : ℚ) = (((A.det.natAbs : ℕ) : ℤ) : ℚ) := by simp
        _ = ((|A.det| : ℤ) : ℚ) := by rw [Int.natCast_natAbs]
        _ = |(A.det : ℚ)| := Int.cast_abs
    rw [← hdc]
    exact hcast

end Work.BW
