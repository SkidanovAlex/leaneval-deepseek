import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.PSL.centralizer_psl_dihedral
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs
import Submission.Work.L2F.Props.centralizer_mk_eq
import Submission.Work.L2F.Props.cmtK0_mulEquiv_hypTorus
import Submission.Work.L2F.Props.mem_cmtK0_iff_exists
import Submission.Work.L2F.Props.conj_eq_inv_of_mem_cmtK0
import Submission.Work.L2F.Props.hypTorus_card_sq
import Submission.Work.L2F.Conic.hypTorus_card
import Submission.Work.L2F.Conic.hypTorus_cyclic
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Aut.realize
import Submission.Work.AUTL2.Aut.centralizer
import Submission.Work.AUTL2.Aut.images
import Submission.Work.AUTL2.Aut.pglIndex
import Submission.Work.AUTL2.Aut.pglHomInjective
import Submission.Work.AUTL2.Galois.decomposition
import Submission.Work.AUTL2.Main.a5odd
import Submission.Work.AUTL2.Normalizer.eq
import Submission.Work.L2F.Props.L2Outer.exists_realization
import Submission.Work.L2F.Props.L2Outer.conj_eq_inv_of_mem_cmtK1
import Submission.Work.L2F.Props.L2Outer.mem_of_odd_index_of_sq_eq_one
import Submission.Work.L2F.Props.isSquare_neg_one_iff_not_isSquare
import Submission.Work.L2F.Props.isSquare_det_iff_mem_toPGL_range

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props

/-! ## Auxiliary arithmetic and the triviality of the centre of `PSL(2,q)` -/

/-- If `q` is odd and `k₁`, `k₂` are odd numbers with `2k = q ± 1`, then `k₁ = k₂`: exactly one of
`(q - 1) / 2` and `(q + 1) / 2` is odd, because `q + 1` and `q - 1` are consecutive even numbers. -/
theorem odd_half_unique {q k₁ k₂ : ℕ} (hq : Odd q) (h₁ : Odd k₁) (h₂ : Odd k₂)
    (e₁ : 2 * k₁ = q + 1 ∨ 2 * k₁ = q - 1)
    (e₂ : 2 * k₂ = q + 1 ∨ 2 * k₂ = q - 1) : k₁ = k₂ := by
  obtain ⟨t, ht⟩ := hq
  obtain ⟨s, hs⟩ := h₁
  obtain ⟨r, hr⟩ := h₂
  have hc₁ : k₁ = t + 1 ∨ k₁ = t := by rcases e₁ with h | h <;> omega
  have hc₂ : k₂ = t + 1 ∨ k₂ = t := by rcases e₂ with h | h <;> omega
  rcases hc₁ with h | h <;> rcases hc₂ with h' | h' <;> omega

/-- `2 ≠ 0` in `GF(p,e)` for an odd prime `p`. -/
theorem two_ne_zero_galois_outer (p e : ℕ) [Fact p.Prime] (hp : Odd p) :
    (2 : GaloisField p e) ≠ 0 := by
  haveI : CharP (GaloisField p e) p := inferInstance
  intro hcon
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p e) p 2).mp hcon
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨m, hm⟩ := hp
  omega

/-- The centre of `PSL(2,q)` is trivial (`q = p ^ e` odd, `q ≥ 5`): an element of the centre
centralizes the image `pslImage` of `PSL(2,q)` in `Sym(ℙ¹)`, whose centralizer is trivial. -/
theorem center_psl_bot (p e : ℕ) [Fact p.Prime] [Fintype (GaloisField p e)]
    [DecidableEq (GaloisField p e)] (hp : Odd p) (hq : 5 ≤ p ^ e) :
    Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e)) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hmem : Work.AUTL2.pslHom (GaloisField p e) z ∈
      Subgroup.centralizer (Work.AUTL2.pslImage (GaloisField p e) :
        Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p e)))) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨x, rfl⟩
    have h := (Subgroup.mem_center_iff.mp hz) x
    rw [← map_mul, ← map_mul, h]
  rw [Work.AUTL2.Aut.centralizer p e hp hq, Subgroup.mem_bot] at hmem
  exact Work.AUTL2.Aut.pslHomInjective (GaloisField p e) (by rw [hmem, map_one])

/-! ## Quotients of dihedral groups, and `DihOrCycSylow` under surjective images -/

/-- A surjective image of a dihedral group (onto a finite group) is cyclic or dihedral. -/
theorem isCyclic_or_dihedralGroup_of_surjective_dihedralGroup {K : Type*} [Group K] [Finite K]
    (n : ℕ) [NeZero n] (f : DihedralGroup n →* K) (hf : Function.Surjective f) :
    IsCyclic K ∨ ∃ m : ℕ, Nonempty (K ≃* DihedralGroup m) := by
  classical
  set a : K := f (DihedralGroup.r 1) with ha
  set b : K := f (DihedralGroup.sr 0) with hb
  have hbsq : b * b = 1 := by rw [hb, ← map_mul, DihedralGroup.sr_mul_self, map_one]
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbsq
  have hconj : b * a * b⁻¹ = a⁻¹ := by
    rw [ha, hb, ← map_inv, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [DihedralGroup.sr_mul_r, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr,
      show (0 : ZMod n) - (0 + 1) = -1 from by ring]
    exact (DihedralGroup.inv_r 1).symm
  -- the two normal forms in `DihedralGroup n`
  have hr : ∀ i : ZMod n, DihedralGroup.r i = (DihedralGroup.r 1 : DihedralGroup n) ^ i.val := by
    intro i
    rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
  have hsr : ∀ i : ZMod n,
      DihedralGroup.sr i = DihedralGroup.sr 0 * (DihedralGroup.r 1 : DihedralGroup n) ^ i.val := by
    intro i
    rw [← hr i, DihedralGroup.sr_mul_r]
    simp
  -- every element of `K` is a rotation `c` or a reflection `b * c`
  have hgen : ∀ y : K, (∃ c ∈ Subgroup.zpowers a, y = c) ∨
      ∃ c ∈ Subgroup.zpowers a, y = b * c := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    rcases Work.AUTL2.dihedral_eq_r_or_sr n x with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · refine Or.inl ⟨a ^ i.val, Subgroup.pow_mem _ (Subgroup.mem_zpowers a) i.val, ?_⟩
      rw [ha, hr i, map_pow]
    · refine Or.inr ⟨a ^ i.val, Subgroup.pow_mem _ (Subgroup.mem_zpowers a) i.val, ?_⟩
      rw [hb, ha, hsr i, map_mul, map_pow]
  by_cases hbC : b ∈ Subgroup.zpowers a
  · -- `K = ⟨a⟩` is cyclic
    left
    have htop : Subgroup.zpowers a = ⊤ := by
      rw [eq_top_iff]
      intro y hy
      rcases hgen y with ⟨c, hc, rfl⟩ | ⟨c, hc, hbc⟩
      · exact hc
      · rw [hbc]
        exact Subgroup.mul_mem _ hbC hc
    haveI : IsCyclic ↥(Subgroup.zpowers a) := inferInstance
    have hcyc : IsCyclic ↥(⊤ : Subgroup K) := htop ▸ inferInstance
    exact (MulEquiv.isCyclic (Subgroup.topEquiv)).mp hcyc
  · -- `⟨a⟩` has index `2` and is inverted by `b`
    right
    have hcyc : IsCyclic ↥(Subgroup.zpowers a) := inferInstance
    have hidx : (Subgroup.zpowers a).index = 2 := by
      rw [Subgroup.index_eq_two_iff_exists_notMem_and']
      refine ⟨b, hbC, fun y => ?_⟩
      rcases hgen y with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
      · exact Or.inr hc
      · exact Or.inl (by rw [← mul_assoc, hbsq, one_mul]; exact hc)
    refine ⟨Nat.card ↥(Subgroup.zpowers a),
      Work.L2F.Dihedral.mulEquiv_dihedral_of_cyclic_index_two (Subgroup.zpowers a) hcyc hidx
        ⟨b, hbC, hbsq, ?_⟩⟩
    intro c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    rw [hbinv]
    calc b * a ^ k * b = (MulAut.conj b) (a ^ k) := by rw [MulAut.conj_apply, hbinv]
      _ = ((MulAut.conj b) a) ^ k := map_zpow (MulAut.conj b) a k
      _ = (a⁻¹) ^ k := by rw [MulAut.conj_apply, hconj]
      _ = (a ^ k)⁻¹ := by rw [_root_.inv_zpow]

/-- A Sylow `2`-subgroup `Q` of `H` is a quotient of a Sylow `2`-subgroup `P` of `G`: namely via
the restriction of `f` to a Sylow subgroup of `G` that maps onto `Q`. -/
theorem sylow_surjective_reduction {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (Q : Sylow 2 H) :
    ∃ (P : Sylow 2 G) (φ : ↥P →* ↥Q), Function.Surjective φ := by
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hf 2 Q
  have hcoe : Subgroup.map f (P : Subgroup G) = (Q : Subgroup H) := by
    rw [← Sylow.coe_mapSurjective hf P, hP]
  let F : ↥P →* H := f.comp (Subgroup.subtype (P : Subgroup G))
  have hF : ∀ x : ↥P, F x ∈ (Q : Subgroup H) := by
    intro x
    rw [← hcoe]
    exact ⟨x.1, x.2, rfl⟩
  refine ⟨P, F.codRestrict (Q : Subgroup H) hF, ?_⟩
  intro y
  have hy : y.1 ∈ Subgroup.map f (P : Subgroup G) := by
    rw [hcoe]
    exact y.2
  obtain ⟨x, hx, hfx⟩ := (Subgroup.mem_map).mp hy
  exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩

/-- `DihOrCycSylow` passes to surjective images. -/
theorem dihOrCycSylow_of_surjective' {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (h : Work.L2F.DihOrCycSylow G) :
    Work.L2F.DihOrCycSylow H := by
  intro Q
  obtain ⟨P, φ, hφ⟩ := sylow_surjective_reduction f hf Q
  rcases h P with hc | ⟨n, ⟨e⟩⟩
  · exact Or.inl (isCyclic_of_surjective φ hφ)
  · let ψ : DihedralGroup n →* ↥Q := φ.comp e.symm.toMonoidHom
    have hψ : Function.Surjective ψ := hφ.comp e.symm.surjective
    haveI hne : NeZero n := by
      haveI : Finite (DihedralGroup n) := e.toEquiv.finite_iff.mp inferInstance
      haveI : Fintype (DihedralGroup n) := Fintype.ofFinite _
      have h2 : Fintype.card (DihedralGroup n) ≠ 0 := Fintype.card_ne_zero
      have h3 : Nat.card (DihedralGroup n) = 2 * n := DihedralGroup.nat_card
      rw [Nat.card_eq_fintype_card] at h3
      exact ⟨by omega⟩
    rcases isCyclic_or_dihedralGroup_of_surjective_dihedralGroup n ψ hψ with hc | ⟨m, ⟨g⟩⟩
    · exact Or.inl hc
    · exact Or.inr ⟨m, ⟨g⟩⟩

/-! ## The model computation: the centralizer of an outer involution of `PGL(2,F)` -/

/-- `Nat.card F` is odd for a finite field `F` with `(2 : F) ≠ 0`. -/
private theorem odd_card_of_two_ne_zero (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) :
    Odd (Nat.card F) := by
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' (K := F)
  haveI := hchar
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h2 ((CharP.cast_eq_zero_iff F 2 2).mpr (dvd_refl 2))
  rw [Nat.card_eq_fintype_card, hcard]
  exact (hp.odd_of_ne_two hp2).pow

/-- The image of `-1 ∈ SL(2,F)` in matrices is the scalar matrix `-1`. -/
private theorem negOne_coe_eq_scalar (F : Type*) [Field F] :
    ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (-1 : F) := by
  show (-1 : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (-1)
  ext i j
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases h : i = j <;> simp [h]

/-- The scalar matrix `c • 1` of `M₂(F)`. -/
private lemma scalar_eq_smul_one (F : Type*) [Semiring F] (c : F) :
    Matrix.scalar (Fin 2) c = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

/-- `toPGL x = 1` for `x ∈ SL(2,F)` (`2 ≠ 0`) iff `x = ±1`. -/
private theorem toPGL_eq_one_iff (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix.SpecialLinearGroup.toPGL x = 1 ↔ x = 1 ∨ x = Work.L2F.negOne F := by
  rw [← MonoidHom.mem_ker, Matrix.SpecialLinearGroup.toPGL_ker,
    Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hx⟩
    have hfac : (r - 1) * (r + 1) = 0 := by
      have h : (r - 1) * (r + 1) = r ^ 2 - 1 := by ring
      rw [h, show r ^ 2 = r ^ Fintype.card (Fin 2) from by simp, hr]
      ring
    rcases mul_eq_zero.mp hfac with h | h
    · left
      refine Subtype.ext ?_
      rw [← hx, sub_eq_zero.mp h]
      simp
    · right
      refine Subtype.ext ?_
      rw [← hx, add_eq_zero_iff_eq_neg.mp h, negOne_coe_eq_scalar]
  · rintro (rfl | rfl)
    · exact ⟨1, by norm_num, by simp⟩
    · refine ⟨-1, by norm_num, ?_⟩
      rw [negOne_coe_eq_scalar]

/-- `cmtK0 F S` is a cyclic group, and its image in `PGL(2,F)` is cyclic of odd order `m` with
`2m = |F| ∓ 1` (the odd one of `(|F| ± 1)/2`). -/
private theorem card_image_cmtK0_aux (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (S : Matrix.GeneralLinearGroup (Fin 2) F) (lam : F)
    (hS : (S : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) = lam • 1)
    (hlam : lam ≠ 0) (hns : ∀ c : F, (S : Matrix (Fin 2) (Fin 2) F) ≠ c • 1)
    (hdet : ¬ IsSquare (S : Matrix (Fin 2) (Fin 2) F).det) :
    IsCyclic ((Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL) ∧
      Odd (Nat.card ((Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL)) ∧
      (2 * Nat.card ((Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL)
          = Nat.card F - 1 ∨
        2 * Nat.card ((Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL)
          = Nat.card F + 1) := by
  classical
  obtain ⟨eK⟩ := Work.L2F.Props.cmtK0_mulEquiv_hypTorus F S lam hS hlam hns
  have hcycK : IsCyclic ↥(Work.L2F.Props.cmtK0 F S) := by
    haveI : IsCyclic ↥(Work.L2F.hypTorus F lam) :=
      Work.L2F.Conic.hypTorus_cyclic F h2 lam hlam
    exact (MulEquiv.isCyclic eK).mpr inferInstance
  have hcardK : Nat.card ↥(Work.L2F.hypTorus F lam)
      = Nat.card ↥(Work.L2F.Props.cmtK0 F S) := (Nat.card_congr eK.toEquiv).symm
  -- `-1 ∈ cmtK0 F S`
  have hmemneg : Work.L2F.negOne F ∈ Work.L2F.Props.cmtK0 F S := by
    rw [Work.L2F.Props.mem_cmtK0_iff_comm]
    rw [show Matrix.SpecialLinearGroup.toGL (Work.L2F.negOne F)
        = Work.L2F.Props.negOneGL F from Units.ext rfl]
    rw [Work.L2F.Props.negOneGL_mul_comm]
  -- the image has half the order of `cmtK0 F S`
  let D := (Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL
  have hD : D = (Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL := rfl
  let gD : ↥(Work.L2F.Props.cmtK0 F S) := ⟨Work.L2F.negOne F, hmemneg⟩
  let φD : ↥(Work.L2F.Props.cmtK0 F S) →* Matrix.ProjGenLinGroup (Fin 2) F :=
    (Matrix.SpecialLinearGroup.toPGL).comp (Work.L2F.Props.cmtK0 F S).subtype
  have hkerD : φD.ker = Subgroup.zpowers gD := by
    apply le_antisymm
    · intro y hy
      rw [MonoidHom.mem_ker] at hy
      rcases (toPGL_eq_one_iff F h2 (y : Matrix.SpecialLinearGroup (Fin 2) F)).mp hy with h | h
      · have hy1 : y = 1 := Subtype.ext h
        rw [hy1]
        exact Subgroup.one_mem _
      · have hyg : y = gD := Subtype.ext h
        rw [hyg]
        exact Subgroup.mem_zpowers gD
    · rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
      change Matrix.SpecialLinearGroup.toPGL (Work.L2F.negOne F) = 1
      exact (toPGL_eq_one_iff F h2 (Work.L2F.negOne F)).mpr (Or.inr rfl)
  have hcardD2 : Nat.card ↥φD.ker = 2 := by
    rw [hkerD, Nat.card_zpowers]
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      apply Subtype.ext
      exact Work.L2F.Involution.negOne_mul_self F
    · intro h
      have h' : (Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) = 1 :=
        congrArg (fun t : ↥(Work.L2F.Props.cmtK0 F S) =>
          (t : Matrix.SpecialLinearGroup (Fin 2) F)) h
      apply h2
      have hmat : (-1 : Matrix (Fin 2) (Fin 2) F) = 1 :=
        congrArg (fun t : Matrix.SpecialLinearGroup (Fin 2) F =>
          (t : Matrix (Fin 2) (Fin 2) F)) h'
      have hentry : -(1 : F) = 1 := by
        have := congrFun (congrFun hmat 0) 0
        simpa using this
      have htwo : (2 : F) = 0 := by
        have h := congrArg (fun t : F => t + 1) hentry
        have h' : (0 : F) = 2 := by simpa [one_add_one_eq_two] using h
        exact h'.symm
      exact htwo
  have hDcard : Nat.card ↥D * 2 = Nat.card ↥(Work.L2F.Props.cmtK0 F S) := by
    have hrange : φD.range = D := by
      rw [hD, MonoidHom.range_comp, Subgroup.range_subtype]
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup φD.ker
    have heq : Nat.card (↥(Work.L2F.Props.cmtK0 F S) ⧸ φD.ker) = Nat.card ↥D := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φD).toEquiv, hrange]
    rw [heq, hcardD2] at hq
    exact hq.symm
  -- the order of the torus
  have hhyp : Nat.card ↥(Work.L2F.hypTorus F lam) = Nat.card F - 1 ∨
      Nat.card ↥(Work.L2F.hypTorus F lam) = Nat.card F + 1 := by
    by_cases hsq : IsSquare lam
    · left
      obtain ⟨c, hc⟩ := hsq
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hc
        exact hlam hc
      exact Work.L2F.Props.hypTorus_card_sq F h2 lam c hc.symm hc0
    · right
      exact Work.L2F.Conic.hypTorus_card F h2 lam hlam (fun a ha => hsq ⟨a, ha.symm⟩)
  -- parity of `(|F| ∓ 1) / 2`
  have hnotneg : ¬ IsSquare (-lam) := by
    rw [← Work.L2F.Props.det_eq_neg_of_sq_eq_smul_one F (S : Matrix (Fin 2) (Fin 2) F) lam hS
      (Work.L2F.Props.trace_eq_zero_of_sq_eq_smul_one F (S : Matrix (Fin 2) (Fin 2) F) lam hS hns)]
    exact hdet
  have hiff := Work.L2F.Props.isSquare_neg_one_iff_not_isSquare F h2 lam hnotneg
  have hFodd : Odd (Nat.card F) := odd_card_of_two_ne_zero F h2
  have hmod : Nat.card F % 4 = 1 ∨ Nat.card F % 4 = 3 := by
    have : Nat.card F % 2 = 1 := Nat.odd_iff.mp hFodd
    omega
  have hOddHyp : Odd (Nat.card ↥(Work.L2F.hypTorus F lam) / 2) := by
    have hsqneg : IsSquare (-1 : F) ↔ Fintype.card F % 4 ≠ 3 :=
      FiniteField.isSquare_neg_one_iff
    have hcardF : Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
    by_cases hsq : IsSquare lam
    · have h1 : ¬ IsSquare (-1 : F) := fun h => (hiff.mp h) hsq
      have h2' : Fintype.card F % 4 = 3 := by
        by_contra hc
        exact h1 (hsqneg.mpr hc)
      obtain ⟨c, hc⟩ := hsq
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hc
        exact hlam hc
      have hval : Nat.card ↥(Work.L2F.hypTorus F lam) = Nat.card F - 1 :=
        Work.L2F.Props.hypTorus_card_sq F h2 lam c hc.symm hc0
      rw [hval, hcardF]
      obtain ⟨k, hk⟩ : ∃ k, Fintype.card F = 4 * k + 3 := by
        refine ⟨Fintype.card F / 4, ?_⟩
        have := Nat.div_add_mod (Fintype.card F) 4
        omega
      exact ⟨k, by omega⟩
    · have h1 : IsSquare (-1 : F) := hiff.mpr hsq
      have h2' : Fintype.card F % 4 = 1 := by
        have h3 : Fintype.card F % 4 ≠ 3 := hsqneg.mp h1
        omega
      have hval : Nat.card ↥(Work.L2F.hypTorus F lam) = Nat.card F + 1 :=
        Work.L2F.Conic.hypTorus_card F h2 lam hlam (fun a ha => hsq ⟨a, ha.symm⟩)
      rw [hval, hcardF]
      obtain ⟨k, hk⟩ : ∃ k, Fintype.card F = 4 * k + 1 := by
        refine ⟨Fintype.card F / 4, ?_⟩
        have := Nat.div_add_mod (Fintype.card F) 4
        omega
      exact ⟨k, by omega⟩
  change IsCyclic ↥D ∧ Odd (Nat.card ↥D) ∧
    (2 * Nat.card ↥D = Nat.card F - 1 ∨ 2 * Nat.card ↥D = Nat.card F + 1)
  have hDorder : 2 * Nat.card ↥D = Nat.card ↥(Work.L2F.hypTorus F lam) := by
    rw [mul_comm, hDcard, ← hcardK]
  have hDeq : Nat.card ↥D = Nat.card ↥(Work.L2F.hypTorus F lam) / 2 := by
    have hdvd : 2 ∣ Nat.card ↥(Work.L2F.hypTorus F lam) := ⟨Nat.card ↥D, hDorder.symm⟩
    have h4 : Nat.card ↥(Work.L2F.hypTorus F lam) / 2 * 2
        = Nat.card ↥(Work.L2F.hypTorus F lam) := Nat.div_mul_cancel hdvd
    omega
  refine ⟨?_, ?_, ?_⟩
  · -- cyclicity of the image
    haveI := hcycK
    refine isCyclic_of_surjective (φD.codRestrict D (fun x => ⟨x, x.2, rfl⟩)) ?_
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  · rw [hDeq]; exact hOddHyp
  · rcases hhyp with h | h
    · exact Or.inl (hDorder.trans h)
    · exact Or.inr (hDorder.trans h)

/-! ## The model computation: the centralizer of an outer involution of `PGL(2,F)` -/

/-- For `π ∈ pglImage F ∖ pslImage F` an involution, the rotation torus
`R = (cmtK0 F S).map pslHom` (for `S` a lift of `π`) is a cyclic subgroup of
`pslImage F ∩ C_{Sym(ℙ¹)}(π)` of order `k'`, inverted by every involution of
`pslImage F ∩ C_{Sym(ℙ¹)}(π)` different from `1`. -/
private theorem outer_involution_model_aux (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h2 : (2 : F) ≠ 0) (π : Equiv.Perm (Work.AUTL2.P1 F)) (hπ : π ∈ Work.AUTL2.pglImage F)
    (hπ' : π ∉ Work.AUTL2.pslImage F) (hπ2 : π * π = 1) (k' : ℕ) (hk' : Odd k')
    (hk'eq : 2 * k' = Nat.card F + 1 ∨ 2 * k' = Nat.card F - 1) :
    ∃ R : Subgroup (Equiv.Perm (Work.AUTL2.P1 F)),
      R ≤ Work.AUTL2.pslImage F ∧
      R ≤ Subgroup.centralizer ({π} : Set (Equiv.Perm (Work.AUTL2.P1 F))) ∧
      Nat.card R = k' ∧ IsCyclic R ∧
      (∀ x ∈ Work.AUTL2.pslImage F,
        x ∈ Subgroup.centralizer ({π} : Set (Equiv.Perm (Work.AUTL2.P1 F))) →
        x ^ 2 = 1 → x ≠ 1 → Work.L2F.Inverts x R) := by
  classical
  obtain ⟨g, hg⟩ := hπ
  obtain ⟨S, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  -- `S * S` is a scalar matrix
  have hgg : Matrix.ProjGenLinGroup.mk S * Matrix.ProjGenLinGroup.mk S = 1 :=
    Work.AUTL2.Aut.pglHomInjective F (by
      show Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk S *
          Matrix.ProjGenLinGroup.mk S) = Work.AUTL2.pglHom F 1
      rw [map_mul, hg, hπ2, map_one])
  have hcenter : S * S ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one, map_mul]
    exact hgg
  obtain ⟨u, hu⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hcenter
  have hS2 : (S : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F)
      = u • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, hu.symm]
    ext i j
    rw [Matrix.smul_apply, Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    by_cases h : i = j <;> simp [h]
  have hu0 : u ≠ 0 := by
    rintro rfl
    have hdet : ((S * S : Matrix.GeneralLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F).det = 0 := by
      rw [← hu]
      simp [Matrix.scalar_apply]
    exact (S * S).det_ne_zero hdet
  -- `S` is not a scalar matrix
  have hns : ∀ c : F, (S : Matrix (Fin 2) (Fin 2) F) ≠ c • 1 := by
    intro c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      have hdet : (S : Matrix (Fin 2) (Fin 2) F).det = 0 := by rw [hc]; simp
      exact S.det_ne_zero hdet
    have hcmem : S ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) := by
      rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
      exact ⟨c, by rw [scalar_eq_smul_one]; exact hc.symm⟩
    have hone : Matrix.ProjGenLinGroup.mk S = 1 := Matrix.ProjGenLinGroup.mk_eq_one.mpr hcmem
    rw [hone, map_one] at hg
    exact hπ' (by rw [← hg]; exact Subgroup.one_mem _)
  -- `det S` is not a square (otherwise `π` would lie in `pslImage`)
  have hdet : ¬ IsSquare (S : Matrix (Fin 2) (Fin 2) F).det := by
    intro hsq
    apply hπ'
    rw [← hg]
    obtain ⟨p, hp⟩ := (Work.L2F.Props.isSquare_det_iff_mem_toPGL_range F S
      (Matrix.ProjGenLinGroup.mk S) rfl).mp hsq
    exact ⟨p, by
      show ((Work.AUTL2.pglHom F).comp Matrix.ProjectiveSpecialLinearGroup.toPGL) p
        = Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk S)
      rw [MonoidHom.comp_apply, hp]⟩
  -- the torus data
  obtain ⟨hPcyc, hPodd, hPcard⟩ :=
    card_image_cmtK0_aux F h2 S u hS2 hu0 hns hdet
  set K := Work.L2F.Props.cmtK0 F S with hK
  set P : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F) :=
    K.map Matrix.SpecialLinearGroup.toPGL with hP
  set R : Subgroup (Equiv.Perm (Work.AUTL2.P1 F)) := P.map (Work.AUTL2.pglHom F) with hR
  have hPmap : P = (Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL := rfl
  have hPcyc' : IsCyclic ↥P := hPcyc
  have hPodd' : Odd (Nat.card ↥P) := hPodd
  have hPcard' : 2 * Nat.card ↥P = Nat.card F - 1 ∨ 2 * Nat.card ↥P = Nat.card F + 1 := hPcard
  have hPcardk : Nat.card ↥P = k' := by
    refine odd_half_unique (odd_card_of_two_ne_zero F h2) hPodd' hk' ?_ hk'eq
    rcases hPcard' with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hRcardk : Nat.card ↥R = k' := by
    rw [Subgroup.card_map_of_injective (Work.AUTL2.Aut.pglHomInjective F), hPcardk]
  refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
  · -- `R ≤ pslImage`
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
    refine ⟨(y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F), ?_⟩
    show Work.AUTL2.pglHom F (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) =
      Work.AUTL2.pglHom F z
    rw [← hyz, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
    rfl
  · -- `R ≤ C(π)`
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
    have hcmt : y ∈ Work.L2F.Props.cmtK F S := Work.L2F.Props.cmtK0_le_cmtK F S hy
    have hcomm : Matrix.SpecialLinearGroup.toPGL y * Matrix.ProjGenLinGroup.mk S =
        Matrix.ProjGenLinGroup.mk S * Matrix.SpecialLinearGroup.toPGL y := by
      change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL y) *
          Matrix.ProjGenLinGroup.mk S =
        Matrix.ProjGenLinGroup.mk S *
          Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL y)
      rw [Work.L2F.Props.mk_mul_comm_mk_iff]
      rcases (Work.L2F.Props.mem_cmtK_iff F S y).mp hcmt with h | h
      · exact ⟨1, by rw [h]; simp⟩
      · exact ⟨-1, by rw [h, Work.L2F.Props.scalar_neg_one_eq_negOneGL]⟩
    rw [← hg, ← hzx, ← hyz]
    rw [← map_mul, ← map_mul, hcomm]
  · -- the order
    exact hRcardk
  · -- cyclicity
    haveI : IsCyclic ↥P := hPcyc'
    refine isCyclic_of_surjective
      (((Work.AUTL2.pglHom F).comp P.subtype).codRestrict R (fun z => ⟨z, z.2, rfl⟩)) ?_
    intro y
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
  · -- involutions of `pslImage ⊓ C(π)` invert `R`
    intro x hxpsl hxcent hxsq hxne r hr
    obtain ⟨z, hz⟩ := hxpsl
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective z
    have hxy : x = Work.AUTL2.pglHom F (Matrix.SpecialLinearGroup.toPGL y) := by
      rw [← hz, ← hy]
      show Work.AUTL2.pslHom F (QuotientGroup.mk y) =
        Work.AUTL2.pglHom F (Matrix.SpecialLinearGroup.toPGL y)
      change Work.AUTL2.pglHom F (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (QuotientGroup.mk y)) = Work.AUTL2.pglHom F (Matrix.SpecialLinearGroup.toPGL y)
      rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
      rfl
    have hcmt : Matrix.SpecialLinearGroup.toPGL y * Matrix.ProjGenLinGroup.mk S =
        Matrix.ProjGenLinGroup.mk S * Matrix.SpecialLinearGroup.toPGL y := by
      have h1 : Work.AUTL2.pglHom F (Matrix.SpecialLinearGroup.toPGL y) *
          Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk S) =
          Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk S) *
            Work.AUTL2.pglHom F (Matrix.SpecialLinearGroup.toPGL y) := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp hxcent
        rw [hxy] at h
        rw [← hg] at h
        exact h
      exact Work.AUTL2.Aut.pglHomInjective F (by rw [map_mul, map_mul]; exact h1)
    have hycmt : y ∈ Work.L2F.Props.cmtK F S := by
      rcases Work.L2F.Props.mk_mul_comm_mk_iff.mp hcmt with ⟨v, hv⟩
      rcases Work.L2F.Props.eq_or_eq_negGL_of_eq_scalar_mul hv with h | h
      · exact (Work.L2F.Props.mem_cmtK_iff F S y).mpr (Or.inl h)
      · exact (Work.L2F.Props.mem_cmtK_iff F S y).mpr (Or.inr h)
    by_cases hy0 : y ∈ Work.L2F.Props.cmtK0 F S
    · -- `x ∈ R` and `x ^ 2 = 1` with `|R| = k'` odd force `x = 1`
      exfalso
      have hxR : x ∈ R := by
        rw [hxy]
        exact ⟨Matrix.SpecialLinearGroup.toPGL y,
          Subgroup.mem_map.mpr ⟨y, hy0, rfl⟩, rfl⟩
      have hxk : x ^ k' = 1 := by
        have h1 : (⟨x, hxR⟩ : ↥R) ^ k' = 1 := by
          rw [← hRcardk, Nat.card_eq_fintype_card]
          exact pow_card_eq_one
        exact Subtype.ext_iff.mp h1
      have hdvd : orderOf x ∣ k' := orderOf_dvd_iff_pow_eq_one.mpr hxk
      have hodd : Odd (orderOf x) := Odd.of_dvd_nat hk' hdvd
      have h2d : orderOf x ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hxsq)
      have hone : orderOf x = 1 := by
        have hle : orderOf x ≤ 2 := Nat.le_of_dvd (by norm_num) h2d
        obtain ⟨a, ha⟩ := hodd
        omega
      exact hxne (orderOf_eq_one_iff.mp hone)
    · -- `y ∈ cmtK1`: `y` inverts the torus
      obtain ⟨z', hz', hz'r⟩ := Subgroup.mem_map.mp hr
      obtain ⟨y', hy', hy'z⟩ := Subgroup.mem_map.mp hz'
      have hy1 : y ∈ Work.L2F.Props.cmtK1 F S := by
        rcases (Work.L2F.Props.mem_cmtK_iff F S y).mp hycmt with h | h
        · exact absurd ((Work.L2F.Props.mem_cmtK0_iff F S y).mpr h) hy0
        · exact h
      have hinv := Work.L2F.Props.L2Outer.conj_eq_inv_of_mem_cmtK1 F S y u hS2
        hu0 hns ((Work.L2F.Props.mem_cmtK1_iff_comm F S y).mp hy1) hy'
      have hr_eq : r = Work.AUTL2.pglHom F (Matrix.SpecialLinearGroup.toPGL y') := by
        rw [← hz'r, ← hy'z]
      calc x * r * x⁻¹ = Work.AUTL2.pglHom F (Matrix.SpecialLinearGroup.toPGL y) *
            Work.AUTL2.pglHom F (Matrix.SpecialLinearGroup.toPGL y') *
            (Work.AUTL2.pglHom F (Matrix.SpecialLinearGroup.toPGL y))⁻¹ := by
            rw [hxy, hr_eq]
        _ = Work.AUTL2.pglHom F (Matrix.SpecialLinearGroup.toPGL (y * y' * y⁻¹)) := by
            simp only [map_mul, map_inv]
        _ = Work.AUTL2.pglHom F (Matrix.SpecialLinearGroup.toPGL y'⁻¹) := by rw [hinv]
        _ = (Work.AUTL2.pglHom F (Matrix.SpecialLinearGroup.toPGL y'))⁻¹ := by
            simp only [map_inv]
        _ = r⁻¹ := by rw [hr_eq]

/-- `L2OuterInvolutionProp`: for `L ⊴ Q` with `L ≅ L₂(q)`, `Q` of cyclic-or-dihedral Sylow 2-type,
and `r ∈ Q` an involution with `r ∉ L·C_Q(L)`, the centralizer `C_L(r)` contains a cyclic `R` of
order `k'` (the odd one of `(q±1)/2`) inverted by every involution of `L` commuting with `r`.
Proof plan:
(1) replace `Q` by `⟨L, r⟩` (the required `R` lies in `L` and is centralized by `r`, so the
statement only involves `L` and `r`; `DihOrCycSylow` is hereditary);
(2) `r ∉ L·C_Q(L)` makes the conjugation action of `r` on `L` a *non-inner* automorphism of order
`2`; the hypothesis `DihOrCycSylow Q` rules out the field-automorphism type (an `r`-invariant
Sylow `S` gives `⟨S, r⟩` a dihedral Sylow with `r` a reflection and `C_{⟨S,r⟩}(r) ≅ V₄`, so the
2-part of `C_L(r)` is at most `4`, while the field type would have a larger 2-part), so the coset
`L·r` corresponds to the `PGL₂(q) ∖ L₂(q)` coset;
(3) the centralizer of an outer involution of `PGL₂(q)` inside `L₂(q)` is dihedral of order `q±1`
(namely `D_{2k'}` for the odd `k'`), and its rotation subgroup is the required cyclic `R`, inverted
by all its involutions (in a dihedral group with odd half-order all involutions act by inversion).
Concretely: model `r` as the image of a matrix `R₀ ∈ GL(2,F)` with `R₀² = λ•1` and
`R₀ ∉ SL·F^•`; then `C_L(r)` is the image in `PSL` of `{x ∈ SL : x R₀ x⁻¹ ∈ F^• R₀}`. -/
theorem L2OuterInvolution : Work.L2F.L2OuterInvolutionProp := by
  intro Q instG instFin L p e instPrime hp hq hLnorm hLiso hdih r hr2 hrnot k' hk'odd hk'eq
  haveI : Fintype (GaloisField p e) := Fintype.ofFinite _
  haveI : DecidableEq (GaloisField p e) := Classical.decEq _
  obtain ⟨eL⟩ := hLiso
  haveI : L.Normal := hLnorm
  -- elementary facts about `F = GF(p,e)`
  have hk0 : e ≠ 0 := by rintro rfl; simp at hq
  have hFcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e hk0
  have h2F : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galois_outer p e hp
  -- the realization of the conjugation action of `Q` on `L`
  obtain ⟨Φ, hΦL, hΦpg, hΦconj, hΦker⟩ :=
    Work.L2F.Props.L2Outer.exists_realization p e hp hq Q L eL
  -- `Φ r` is an involution
  have hr_sq : r * r = 1 := by
    have h := pow_orderOf_eq_one r
    rw [hr2] at h
    simpa [pow_two] using h
  have hπsq : Φ r * Φ r = 1 := by rw [← map_mul, hr_sq, map_one]
  -- the range of `Φ`
  have hΦrange_le : Φ.range ≤ Work.AUTL2.pgammaL (GaloisField p e) := by
    rintro _ ⟨q, rfl⟩
    exact hΦpg q
  have hpsl_le : Work.AUTL2.pslImage (GaloisField p e) ≤ Φ.range := by
    rintro _ ⟨x, rfl⟩
    refine ⟨eL.symm x, ?_⟩
    rw [hΦL, MulEquiv.apply_symm_apply]
  have hdih_range : Work.L2F.DihOrCycSylow ↥Φ.range :=
    dihOrCycSylow_of_surjective' Φ.rangeRestrict Φ.rangeRestrict_surjective hdih
  have hodd := Work.AUTL2.Main.a5odd p e hp hq Φ.range hΦrange_le hpsl_le hdih_range
  -- `Φ r` is not in `pslImage`: that would put `r` into `L · C_Q(L)`
  have hπnot : Φ r ∉ Work.AUTL2.pslImage (GaloisField p e) := by
    rintro ⟨x, hx⟩
    have h1 : Φ ((eL.symm x : ↥L) : Q) = Work.AUTL2.pslHom (GaloisField p e) x := by
      rw [hΦL, MulEquiv.apply_symm_apply]
    have h2 : Φ (r * ((eL.symm x : ↥L) : Q)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, ← hx, mul_inv_cancel]
    have hker : r * ((eL.symm x : ↥L) : Q)⁻¹ ∈ Subgroup.centralizer (L : Set Q) :=
      (hΦker _).mp h2
    have hmem : r ∈ L ⊔ Subgroup.centralizer (L : Set Q) := by
      have hA : r * ((eL.symm x : ↥L) : Q)⁻¹ ∈ L ⊔ Subgroup.centralizer (L : Set Q) :=
        (le_sup_right : Subgroup.centralizer (L : Set Q) ≤
          L ⊔ Subgroup.centralizer (L : Set Q)) hker
      have hB : ((eL.symm x : ↥L) : Q) ∈ L ⊔ Subgroup.centralizer (L : Set Q) :=
        (le_sup_left : L ≤ L ⊔ Subgroup.centralizer (L : Set Q)) (eL.symm x).2
      have hprod : (r * ((eL.symm x : ↥L) : Q)⁻¹) * ((eL.symm x : ↥L) : Q) = r := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
      rw [← hprod]
      exact mul_mem hA hB
    exact hrnot hmem
  -- `Φ r` lies in `pglImage` (this is the content of `DihOrCycSylow Q`)
  have hπpgl : Φ r ∈ Work.AUTL2.pglImage (GaloisField p e) := by
    have hpglN : Work.AUTL2.pgammaL (GaloisField p e) ≤
        Subgroup.normalizer (Work.AUTL2.pglImage (GaloisField p e) :
          Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p e)))) := by
      rw [Work.AUTL2.pgammaL]
      exact sup_le Subgroup.le_normalizer
        (Work.AUTL2.Galois.galSub_le_normalizer_pglImage _)
    have hN : ((Φ.range ⊓ Work.AUTL2.pglImage (GaloisField p e)).subgroupOf Φ.range).Normal := by
      rw [Subgroup.normal_subgroupOf_iff inf_le_left]
      intro h k hh hk
      rw [Subgroup.mem_inf] at hh ⊢
      refine ⟨?_, ?_⟩
      · exact Φ.range.mul_mem (Φ.range.mul_mem hk hh.1) (Φ.range.inv_mem hk)
      · exact (Subgroup.mem_normalizer_iff.mp (hpglN (hΦrange_le hk)) h).mp hh.2
    haveI := hN
    have hmem := Work.L2F.Props.L2Outer.mem_of_odd_index_of_sq_eq_one
      ((Φ.range ⊓ Work.AUTL2.pglImage (GaloisField p e)).subgroupOf Φ.range)
      (x := (⟨Φ r, ⟨r, rfl⟩⟩ : ↥Φ.range)) hodd (Subtype.ext hπsq)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hmem
    exact hmem.2
  -- the abstract model computation
  obtain ⟨R, hR_psl, hR_cent, hR_card, hR_cyc, hR_inv⟩ :=
    outer_involution_model_aux (GaloisField p e) h2F (Φ r) hπpgl hπnot hπsq k' hk'odd
      (by rw [hFcard]; exact hk'eq)
  -- pull `R` back to `L`
  let ψ : ↥L →* Equiv.Perm (Work.AUTL2.P1 (GaloisField p e)) :=
    (Work.AUTL2.pslHom (GaloisField p e)).comp eL.toMonoidHom
  have hψcoe : ∀ y : ↥L, ψ y = Φ (y : Q) := fun y => (hΦL y).symm
  have hψinj : Function.Injective ψ := by
    intro a b hab
    exact eL.injective (Work.AUTL2.Aut.pslHomInjective (GaloisField p e) hab)
  have hψrange : ψ.range = Work.AUTL2.pslImage (GaloisField p e) := by
    ext g
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨eL y, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨eL.symm x, by simp [ψ]⟩
  let R' : Subgroup ↥L := R.comap ψ
  let RL : Subgroup Q := R'.map L.subtype
  have hR'map : R'.map ψ = R :=
    Subgroup.map_comap_eq_self (f := ψ) (H := R) (by rw [hψrange]; exact hR_psl)
  -- `L ⊓ C_Q(L) = 1` (the centre of `L ≅ PSL(2,q)` is trivial)
  have hcenterL : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hcent : eL z ∈ Subgroup.center
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      calc y * eL z = eL (eL.symm y) * eL z := by rw [MulEquiv.apply_symm_apply]
        _ = eL (eL.symm y * z) := (map_mul eL _ _).symm
        _ = eL (z * eL.symm y) := by rw [(Subgroup.mem_center_iff.mp hz) (eL.symm y)]
        _ = eL z * eL (eL.symm y) := map_mul eL _ _
        _ = eL z * y := by rw [MulEquiv.apply_symm_apply]
    rw [center_psl_bot p e hp hq, Subgroup.mem_bot] at hcent
    exact eL.injective (by rw [hcent, map_one])
  have hZL : L ⊓ Subgroup.centralizer (L : Set Q) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_inf] at hz
    obtain ⟨hzL, hzC⟩ := hz
    rw [Subgroup.mem_bot]
    have hcent : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hzC) (w : Q) w.2
    rw [hcenterL, Subgroup.mem_bot] at hcent
    exact Subtype.ext_iff.mp hcent
  -- `RL` is the required witness
  refine ⟨RL, Subgroup.map_subtype_le R', ?_, ?_, ?_, ?_⟩
  · -- `RL ≤ C_Q(r)`
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
    change (y₀ : Q) * r = r * (y₀ : Q)
    have hcomm : ψ y₀ * Φ r = Φ r * ψ y₀ :=
      Subgroup.mem_centralizer_singleton_iff.mp (hR_cent (show ψ y₀ ∈ R from hy₀))
    have hker : (y₀ : Q) * r * (y₀ : Q)⁻¹ * r⁻¹ ∈ Subgroup.centralizer (L : Set Q) := by
      apply (hΦker _).mp
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hψcoe y₀, hcomm]
      simp
    have hL : (y₀ : Q) * r * (y₀ : Q)⁻¹ * r⁻¹ ∈ L := by
      have h1 : r * (y₀ : Q)⁻¹ * r⁻¹ ∈ L := hLnorm.conj_mem (y₀ : Q)⁻¹ (L.inv_mem y₀.2) r
      have h2 : (y₀ : Q) * (r * (y₀ : Q)⁻¹ * r⁻¹) ∈ L := L.mul_mem y₀.2 h1
      rwa [show (y₀ : Q) * (r * (y₀ : Q)⁻¹ * r⁻¹) =
          (y₀ : Q) * r * (y₀ : Q)⁻¹ * r⁻¹ from by group] at h2
    have ht : (y₀ : Q) * r * (y₀ : Q)⁻¹ * r⁻¹ = 1 := by
      have hmem : (y₀ : Q) * r * (y₀ : Q)⁻¹ * r⁻¹ ∈ L ⊓ Subgroup.centralizer (L : Set Q) :=
        ⟨hL, hker⟩
      rw [hZL, Subgroup.mem_bot] at hmem
      exact hmem
    rw [show (y₀ : Q) * r
          = ((y₀ : Q) * r * (y₀ : Q)⁻¹ * r⁻¹) * (r * (y₀ : Q)) by group, ht, one_mul]
  · -- the order
    have h1 : Nat.card RL = Nat.card R' := Subgroup.card_map_of_injective Subtype.coe_injective
    have h2 : Nat.card R' = Nat.card R := by
      have hc := Subgroup.card_map_of_injective (f := ψ) hψinj (K := R')
      rw [hR'map] at hc
      exact hc.symm
    rw [h1, h2, hR_card]
  · -- cyclicity
    have hR'cyc : IsCyclic ↥R' := by
      have he := Subgroup.equivMapOfInjective R' ψ hψinj
      rw [hR'map] at he
      exact (MulEquiv.isCyclic he).mpr hR_cyc
    have he2 := Subgroup.equivMapOfInjective R' L.subtype Subtype.coe_injective
    exact (MulEquiv.isCyclic he2).mp hR'cyc
  · -- every involution of `L` commuting with `r` inverts `RL`
    intro x hxL hx2 hxr y hy
    obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
    have hxsq : x * x = 1 := by
      have h := pow_orderOf_eq_one x
      rw [hx2] at h
      simpa [pow_two] using h
    have hxne : x ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hx2
      exact absurd hx2 (by norm_num)
    have hxcent : Φ x ∈ Subgroup.centralizer ({Φ r} :
        Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p e)))) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← map_mul, hxr, map_mul]
    have hxpsl : Φ x ∈ Work.AUTL2.pslImage (GaloisField p e) :=
      ⟨eL ⟨x, hxL⟩, (hΦL ⟨x, hxL⟩).symm⟩
    have hxsq' : (Φ x) ^ 2 = 1 := by rw [pow_two, ← map_mul, hxsq, map_one]
    have hxne' : Φ x ≠ 1 := by
      intro h
      have h1 : ψ ⟨x, hxL⟩ = 1 := by rw [hψcoe]; exact h
      have h2 : (⟨x, hxL⟩ : ↥L) = 1 := hψinj (by rw [h1, map_one])
      exact hxne (Subtype.ext_iff.mp h2)
    have hinv := hR_inv (Φ x) hxpsl hxcent hxsq' hxne'
    have h1 := hinv (ψ y₀) hy₀
    rw [← hψcoe ⟨x, hxL⟩] at h1
    have hker : ((x * (y₀ : Q) * x⁻¹) * (y₀ : Q)) ∈ Subgroup.centralizer (L : Set Q) := by
      apply (hΦker _).mp
      rw [map_mul, map_mul, map_mul, map_inv, ← hψcoe ⟨x, hxL⟩, ← hψcoe y₀, h1]
      exact inv_mul_cancel _
    have hL : ((x * (y₀ : Q) * x⁻¹) * (y₀ : Q)) ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem hxL y₀.2) (L.inv_mem hxL)) y₀.2
    have ht : ((x * (y₀ : Q) * x⁻¹) * (y₀ : Q)) = 1 := by
      have hmem : ((x * (y₀ : Q) * x⁻¹) * (y₀ : Q)) ∈
          L ⊓ Subgroup.centralizer (L : Set Q) := ⟨hL, hker⟩
      rw [hZL, Subgroup.mem_bot] at hmem
      exact hmem
    have hfin : x * (y₀ : Q) * x⁻¹ = (y₀ : Q)⁻¹ := by
      rw [show x * (y₀ : Q) * x⁻¹
            = ((x * (y₀ : Q) * x⁻¹) * (y₀ : Q)) * (y₀ : Q)⁻¹ by group,
        ht, one_mul]
    simpa using hfin

end Work.L2F.Props
