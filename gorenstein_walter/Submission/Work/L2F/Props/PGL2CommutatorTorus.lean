import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs
import Submission.Work.L2F.Props.centralizer_mk_eq
import Submission.Work.L2F.Props.mem_cmtK0_iff_exists
import Submission.Work.L2F.Props.cmtK0_mulEquiv_hypTorus
import Submission.Work.L2F.Props.hypTorus_card_sq
import Submission.Work.L2F.Props.isSquare_neg_one_iff_not_isSquare
import Submission.Work.L2F.Props.mod_four_eq_one_iff_isSquare_neg_one
import Submission.Work.L2F.Props.conj_eq_inv_of_mem_cmtK0
import Submission.Work.L2F.Props.card_map_cmtK0
import Submission.Work.L2F.Props.map_cmtK0_ne
import Submission.Work.L2F.Props.exists_lift_setup
import Submission.Work.L2F.Props.four_dvd_pgl_torus
import Submission.Work.L2F.Props.commutator_zpowers_map_cmtK_eq
import Submission.Work.L2F.Conic.hypTorus_card
import Submission.Work.L2F.Conic.hypTorus_cyclic
import Submission.Work.L2F.Main

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props

variable (F : Type*) [Field F]

/-- The range of `ProjectiveSpecialLinearGroup.toPGL` is `SLsub F`. -/
theorem range_toPGL_eq :
    (Matrix.ProjectiveSpecialLinearGroup.toPGL :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F →* Matrix.ProjGenLinGroup (Fin 2) F).range =
      SLsub F := by
  apply le_antisymm
  · rintro g ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) x
    exact ⟨y, rfl⟩
  · rintro g ⟨y, rfl⟩
    exact ⟨QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) y, rfl⟩

/-- `S * toGL T` squares to `lam • 1` when `S² = lam • 1`, `T² = -1` and `T S = - S T`. -/
theorem mul_toGL_sq (S : Matrix.GeneralLinearGroup (Fin 2) F)
    (T : Matrix.SpecialLinearGroup (Fin 2) F) (lam : F)
    (hS : (S : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) = lam • 1)
    (hT2 : (T : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F) = -1)
    (hTS : (T : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) =
      -((S : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F))) :
    (((S * Matrix.SpecialLinearGroup.toGL T : Matrix.GeneralLinearGroup (Fin 2) F)) :
        Matrix (Fin 2) (Fin 2) F) *
      (((S * Matrix.SpecialLinearGroup.toGL T : Matrix.GeneralLinearGroup (Fin 2) F)) :
        Matrix (Fin 2) (Fin 2) F) = lam • 1 := by
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  calc (S : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F) *
        ((S : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F))
      = (S : Matrix (Fin 2) (Fin 2) F) *
          ((T : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F)) *
            (T : Matrix (Fin 2) (Fin 2) F) := by simp only [mul_assoc]
    _ = (S : Matrix (Fin 2) (Fin 2) F) *
          (-((S : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F))) *
            (T : Matrix (Fin 2) (Fin 2) F) := by rw [hTS]
    _ = -(((S : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F)) *
          ((T : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F))) := by
        simp only [mul_neg, neg_mul, mul_assoc]
    _ = -((lam • 1) * (-1)) := by rw [hS, hT2]
    _ = lam • 1 := by rw [mul_neg, mul_one, neg_neg]


/-- The anticommutation `T S = - S T` transfers to `S * toGL T`. -/
theorem mul_toGL_hST (S : Matrix.GeneralLinearGroup (Fin 2) F)
    (T : Matrix.SpecialLinearGroup (Fin 2) F)
    (hT2 : (T : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F) = -1)
    (hTS : (T : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) =
      -((S : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F))) :
    (T : Matrix (Fin 2) (Fin 2) F) *
        (((S * Matrix.SpecialLinearGroup.toGL T : Matrix.GeneralLinearGroup (Fin 2) F)) :
          Matrix (Fin 2) (Fin 2) F) =
      -((((S * Matrix.SpecialLinearGroup.toGL T : Matrix.GeneralLinearGroup (Fin 2) F)) :
          Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F)) := by
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  have h1 : (T : Matrix (Fin 2) (Fin 2) F) * ((S : Matrix (Fin 2) (Fin 2) F) *
      (T : Matrix (Fin 2) (Fin 2) F)) = (S : Matrix (Fin 2) (Fin 2) F) := by
    rw [← mul_assoc, hTS, neg_mul, mul_assoc, hT2, mul_neg, mul_one, neg_neg]
  have h2 : -(((S : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F)) *
      (T : Matrix (Fin 2) (Fin 2) F)) = (S : Matrix (Fin 2) (Fin 2) F) := by
    rw [mul_assoc, hT2, mul_neg, mul_one, neg_neg]
  rw [h1, h2]

/-- The determinant of `S * toGL T` is that of `S`. -/
theorem mul_toGL_det (S : Matrix.GeneralLinearGroup (Fin 2) F)
    (T : Matrix.SpecialLinearGroup (Fin 2) F) (hT2 : (T : Matrix (Fin 2) (Fin 2) F) *
      (T : Matrix (Fin 2) (Fin 2) F) = -1) :
    (((S * Matrix.SpecialLinearGroup.toGL T : Matrix.GeneralLinearGroup (Fin 2) F)) :
        Matrix (Fin 2) (Fin 2) F).det = (S : Matrix (Fin 2) (Fin 2) F).det := by
  have hTdet : (T : Matrix (Fin 2) (Fin 2) F).det = 1 := Matrix.SpecialLinearGroup.det_coe T
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  rw [Matrix.det_mul, hTdet, mul_one]

/-- `S * toGL T` is not scalar when `det S` is not a square. -/
theorem mul_toGL_not_scalar (S : Matrix.GeneralLinearGroup (Fin 2) F)
    (T : Matrix.SpecialLinearGroup (Fin 2) F)
    (hT2 : (T : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F) = -1)
    (hdet : ¬ IsSquare (S : Matrix (Fin 2) (Fin 2) F).det) :
    ∀ c : F, (((S * Matrix.SpecialLinearGroup.toGL T :
      Matrix.GeneralLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) ≠ c • 1 := by
  intro c hc
  refine hdet ⟨c, ?_⟩
  have h := mul_toGL_det F S T hT2
  rw [← h, hc, Matrix.det_smul, Matrix.det_one, Fintype.card_fin]
  ring

/-- `toPGL T` inverts the image of the torus `cmtK0 F S`. -/
theorem inverts_toPGL_map_cmtK0 (S : Matrix.GeneralLinearGroup (Fin 2) F)
    (T : Matrix.SpecialLinearGroup (Fin 2) F) (lam : F)
    (hS : (S : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) = lam • 1)
    (hlam : lam ≠ 0) (hns : ∀ c : F, (S : Matrix (Fin 2) (Fin 2) F) ≠ c • 1)
    (hT2 : (T : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F) = -1)
    (hST : Matrix.SpecialLinearGroup.toGL T * S = negGL F S *
      Matrix.SpecialLinearGroup.toGL T) :
    Work.L2F.Inverts (Matrix.SpecialLinearGroup.toPGL T)
      ((cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  have hconj := conj_eq_inv_of_mem_cmtK0 F S T lam hS hlam hns hT2 hST hx
  rw [← map_inv, ← map_mul, ← map_mul, hconj, map_inv]

/-- `PGL2CommutatorTorusProp` (Theorem 2.6 step 2): for an involution `t ∈ L₂(q)` and an involution
`s ∈ PGL₂(q) \ L₂(q)` commuting with `t`, the groups `R = [⟨t⟩, C_L(s)]` and `R' = [⟨t⟩, C_L(ts)]`
are cyclic of order `m = (q+ε)/2` with `ε = 1` for `q ≡ 1 (mod 4)` and `ε = -1` for `q ≡ 3 (mod 4)`,
are inverted by `t`, and `⟨t, R, R'⟩` has order divisible by 4.
Proof (matrix level, over `GL(2,F)`): lift `s` to `S ∈ GL(2,F)` with `S² = λ•1`, `S ∉ SL·F^•`; then
`C_L(s)` is the image in `SL` of `{x ∈ SL : x S x⁻¹ ∈ F^• S}`, which is the "anti-diagonal" torus
relative to the `S`-inversion, a dihedral group of order `q+ε` whose rotation subgroup is cyclic of
order `m`; `t` (with lift `T`, `T² = -1`) acts by inversion on it, so `[T, C_L(s)]` is that rotation
subgroup, cyclic of order `m` and inverted by `t`.  Repeating with the lift `S*T` of `t*s` (which
anticommutes with `T` for the sign `S T = -T S` that `s ∉ L` enforces) gives `R'`, and `R ≠ R'`
(they lie in different tori of `L`), so `⟨t, R, R'⟩` has order divisible by 4. -/
theorem PGL2CommutatorTorus : Work.L2F.PGL2CommutatorTorusProp := by
  intro p k inst hp hk t s ht hs hcomm htL hsL
  classical
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  have h2 : (2 : GaloisField p k) ≠ 0 := Work.L2F.two_ne_zero_galois hp
  have hcard : Nat.card (GaloisField p k) = p ^ k := Work.L2F.card_galois hk
  have hfive : 5 ≤ Nat.card (GaloisField p k) := by rw [hcard]; exact hk
  obtain ⟨S, T, lam, hlam, hSmk, hT, hS2, hT2, hST, hdetns, hnsS⟩ :=
    exists_lift_setup (GaloisField p k) h2 t s ht hs hcomm htL hsL
  -- matrix form of the anticommutation
  have hTSmat : (T : Matrix (Fin 2) (Fin 2) (GaloisField p k)) *
      (S : Matrix (Fin 2) (Fin 2) (GaloisField p k)) =
      -((S : Matrix (Fin 2) (Fin 2) (GaloisField p k)) *
        (T : Matrix (Fin 2) (Fin 2) (GaloisField p k))) := by
    have h := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) (GaloisField p k) =>
      (g : Matrix (Fin 2) (Fin 2) (GaloisField p k))) hST
    simpa only [Matrix.GeneralLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      negGL_apply, negOneGL_apply, Matrix.neg_mul, Matrix.one_mul] using h
  -- the facts for the second lift `S * toGL T`
  have hS'2 := mul_toGL_sq (GaloisField p k) S T lam hS2 hT2 hTSmat
  have hST'mat := mul_toGL_hST (GaloisField p k) S T hT2 hTSmat
  have hdetns' : ¬ IsSquare ((((S * Matrix.SpecialLinearGroup.toGL T :
      Matrix.GeneralLinearGroup (Fin 2) (GaloisField p k))) :
      Matrix (Fin 2) (Fin 2) (GaloisField p k)).det) := by
    rw [mul_toGL_det (GaloisField p k) S T hT2]
    exact hdetns
  have hnsS' : ∀ c : GaloisField p k, (((S * Matrix.SpecialLinearGroup.toGL T :
      Matrix.GeneralLinearGroup (Fin 2) (GaloisField p k))) :
      Matrix (Fin 2) (Fin 2) (GaloisField p k)) ≠ c • 1 :=
    mul_toGL_not_scalar (GaloisField p k) S T hT2 hdetns
  have hST' : Matrix.SpecialLinearGroup.toGL T *
      (S * Matrix.SpecialLinearGroup.toGL T) =
      negGL (GaloisField p k) (S * Matrix.SpecialLinearGroup.toGL T) *
        Matrix.SpecialLinearGroup.toGL T := by
    apply Units.ext
    simpa only [Matrix.GeneralLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      negGL_apply, negOneGL_apply, Matrix.neg_mul, Matrix.one_mul] using hST'mat
  have hT' : Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL T) = t := hT
  have hmkS' : Matrix.ProjGenLinGroup.mk (S * Matrix.SpecialLinearGroup.toGL T) = t * s := by
    rw [map_mul, hSmk, hT']
    exact hcomm.symm
  -- cyclicity, order and oddness of the two tori
  obtain ⟨hcycS, hcardS, hoddS⟩ :=
    card_map_cmtK0 (GaloisField p k) h2 (p ^ k) hcard S lam hS2 hlam hnsS hdetns
  obtain ⟨hcycS', hcardS', hoddS'⟩ :=
    card_map_cmtK0 (GaloisField p k) h2 (p ^ k) hcard (S * Matrix.SpecialLinearGroup.toGL T)
      lam hS'2 hlam hnsS' hdetns'
  -- the two commutator subgroups
  have hR : ⁅Subgroup.zpowers t, (Matrix.ProjectiveSpecialLinearGroup.toPGL :
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k) →*
          Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)).range ⊓
        Subgroup.centralizer ({s} : Set (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)))⁆ =
      (cmtK0 (GaloisField p k) S).map Matrix.SpecialLinearGroup.toPGL := by
    rw [range_toPGL_eq (GaloisField p k), ← hSmk, ← hT,
      centralizer_mk_eq (GaloisField p k) S lam hS2 hlam]
    exact commutator_zpowers_map_cmtK_eq (GaloisField p k) S T lam hS2 hlam hnsS hT2 hST hoddS
  have hR' : ⁅Subgroup.zpowers t, (Matrix.ProjectiveSpecialLinearGroup.toPGL :
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k) →*
          Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)).range ⊓
        Subgroup.centralizer ({t * s} :
          Set (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)))⁆ =
      (cmtK0 (GaloisField p k) (S * Matrix.SpecialLinearGroup.toGL T)).map
        Matrix.SpecialLinearGroup.toPGL := by
    rw [range_toPGL_eq (GaloisField p k), ← hmkS', ← hT,
      centralizer_mk_eq (GaloisField p k) (S * Matrix.SpecialLinearGroup.toGL T) lam hS'2 hlam]
    exact commutator_zpowers_map_cmtK_eq (GaloisField p k)
      (S * Matrix.SpecialLinearGroup.toGL T) T lam hS'2 hlam hnsS' hT2 hST' hoddS'
  -- inversion
  have hInv : Work.L2F.Inverts t
      ((cmtK0 (GaloisField p k) S).map Matrix.SpecialLinearGroup.toPGL) := by
    rw [← hT]
    exact inverts_toPGL_map_cmtK0 (GaloisField p k) S T lam hS2 hlam hnsS hT2 hST
  have hInv' : Work.L2F.Inverts t
      ((cmtK0 (GaloisField p k) (S * Matrix.SpecialLinearGroup.toGL T)).map
        Matrix.SpecialLinearGroup.toPGL) := by
    rw [← hT]
    exact inverts_toPGL_map_cmtK0 (GaloisField p k) (S * Matrix.SpecialLinearGroup.toGL T) T
      lam hS'2 hlam hnsS' hT2 hST'
  dsimp only
  rw [hR, hR']
  exact ⟨hcycS, hcycS', hcardS, hcardS', hInv, hInv',
    four_dvd_pgl_torus (GaloisField p k) h2 (p ^ k) hcard _ _ hcardS hcardS' hcycS hcycS'
      (map_cmtK0_ne (GaloisField p k) h2 hfive S T lam hS2 hlam hnsS hdetns hT2 hST) t ht
      hInv hInv'⟩

end Work.L2F.Props
