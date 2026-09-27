import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.clutchIdem_cls_indep
import Submission.Work.KT.whitehead_diag
import Submission.Work.KT.ExtGen.disc_square
import Submission.Work.KT.Fund.kappa_add_blocks
import Submission.Work.KT.Fund.kappa_one_alt

/-!
# `Work.KT.Fund.kappa_mul` — multiplicativity of the clutching class

For commuting units `u`, `v` over `C(X × S¹, ℂ)` (commutativity is in fact not needed):

  `κ(u * v) = κ(u) + κ(v) - cls (Mat.one C(X × S², ℂ) n)`,

i.e. the reduced clutching class `κ(u) - cls (1)` is a group homomorphism from the pointwise
product of units to `K⁰(X × S²)`.

## Proof

Put `U := diag(u,v)`, `U' := diag(uv,1)` and `E := diag(v⁻¹,v)` (all `2n × 2n` matrices over the
circle algebra).  The elementary identity `diag(u,v) = diag(uv,1) · diag(v⁻¹,v)` exhibits `U` as a
right multiple of `U'` by `E`, and by **Whitehead's lemma** (`Work.KT.whitehead_diag`) `E` is a
product of elementary matrices.  Each elementary matrix lifts to an *invertible* matrix over the
disc (its entry lifts by Tietze, `slift`), so `E` does too (`exists_lift_list`); and

* `kappa_wmul_eq`: `κ` is unchanged by right multiplication with a unit that has an invertible lift
  to the disc — the algebraic heart, proved through the Murray–von Neumann equivalence of the two
  clutched idempotents: conjugation by `Θ = diag(Mt,1)` carries the two disc projections of `W · M`
  to projections with the same images as those of `W`, compatibly on the equator;
* `kappa_add_blocks`: `κ (u₁ ⊕ u₂) = κ u₁ + κ u₂` for block-diagonal clutching functions;
* `kappa_one_alt`: `κ(1) = cls (Mat.one C(X × S², ℂ) n)`.

Chaining, `κ(u) + κ(v) = κ(diag(u,v)) = κ(diag(uv,1)) = κ(uv) + κ(1)`, which is the claim.
-/

set_option maxHeartbeats 4000000

open Matrix

namespace Work.KT.Fund

noncomputable section

local notation "Circ[" X "]" => C(X × Sph ℂ, ℂ)
local notation "Disc[" X "]" => C(X × Ball ℂ, ℂ)


/-- The `2n × n` matrix with block rows `A` (top) and `B` (bottom). -/
def colBlock (R : Type) [Zero R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n ⊕ Fin n) (Fin n) R :=
  fun i j => match i with | Sum.inl a => A a j | Sum.inr a => B a j

lemma graphB_eq_colBlock (R : Type) [Ring R] {n : ℕ} (F : Matrix (Fin n) (Fin n) R) :
    graphB R F = colBlock R 1 F := by
  ext i j
  cases i <;> simp [graphB, colBlock, Matrix.one_apply]

lemma recipB_eq_colBlock (R : Type) [Ring R] {n : ℕ} (G : Matrix (Fin n) (Fin n) R) :
    recipB R G = colBlock R G 1 := by
  ext i j
  cases i <;> simp [recipB, colBlock, Matrix.one_apply]

lemma blkDiag_mul_colBlock (R : Type) [Ring R] {n : ℕ}
    (Mt A B : Matrix (Fin n) (Fin n) R) :
    (Matrix.fromBlocks Mt 0 0 (1 : Matrix (Fin n) (Fin n) R)) * colBlock R A B
      = colBlock R (Mt * A) B := by
  ext i j
  cases i with
  | inl a =>
    simp only [colBlock, Matrix.mul_apply, Matrix.fromBlocks, Fintype.sum_sum_type,
      Matrix.of_apply]
    simp
  | inr a =>
    simp only [colBlock, Matrix.mul_apply, Matrix.fromBlocks, Fintype.sum_sum_type,
      Matrix.of_apply]
    simp [Matrix.one_apply]

lemma colBlock_mul (R : Type) [Ring R] {n : ℕ}
    (A B Mt : Matrix (Fin n) (Fin n) R) :
    colBlock R A B * Mt = colBlock R (A * Mt) (B * Mt) := by
  ext i j
  cases i <;> simp [colBlock, Matrix.mul_apply]

theorem orthProj_conj_left {R : Type} [CommRing R] [StarRing R] {n : ℕ}
    (B B' : Matrix (Fin n ⊕ Fin n) (Fin n) R) (Mt Mtinv : Matrix (Fin n) (Fin n) R)
    (Θ Θinv : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (hB : Θ * B' = B * Mt) (hB' : Θinv * B = B' * Mtinv) (hMt : Mt * Mtinv = 1)
    (hhB : IsUnit (Bᴴ * B)) (hhB' : IsUnit (B'ᴴ * B')) :
    (orthProj R B * (Θ * orthProj R B' * Θinv) = Θ * orthProj R B' * Θinv) ∧
    ((Θ * orthProj R B' * Θinv) * orthProj R B = orthProj R B) := by
  constructor
  · simp only [orthProj, Matrix.mul_assoc]
    have hgen : ∀ X : Matrix (Fin n) (Fin n ⊕ Fin n) R,
        Ring.inverse (Bᴴ * B) * (Bᴴ * (Θ * (B' * X))) = Mt * X := by
      intro X
      have h2' : Bᴴ * (Θ * B') = (Bᴴ * B) * Mt := by rw [hB, Matrix.mul_assoc]
      have h2 : Bᴴ * (Θ * (B' * X)) = (Bᴴ * B) * (Mt * X) := by
        rw [← Matrix.mul_assoc Θ B' X, ← Matrix.mul_assoc Bᴴ (Θ * B') X, h2',
          ← Matrix.mul_assoc (Bᴴ * B) Mt X]
      rw [h2, ← Matrix.mul_assoc (Ring.inverse (Bᴴ * B)) (Bᴴ * B) (Mt * X),
        Ring.inverse_mul_cancel _ hhB, Matrix.one_mul]
    rw [hgen]
    rw [← Matrix.mul_assoc Θ B' (Ring.inverse (B'ᴴ * B') * (B'ᴴ * Θinv)), hB]
    rw [Matrix.mul_assoc B Mt]
  · simp only [orthProj, Matrix.mul_assoc]
    have hgen' : ∀ X : Matrix (Fin n) (Fin n ⊕ Fin n) R,
        Ring.inverse (B'ᴴ * B') * (B'ᴴ * (Θinv * (B * X))) = Mtinv * X := by
      intro X
      have h2' : B'ᴴ * (Θinv * B) = (B'ᴴ * B') * Mtinv := by rw [hB', Matrix.mul_assoc]
      have h2 : B'ᴴ * (Θinv * (B * X)) = (B'ᴴ * B') * (Mtinv * X) := by
        rw [← Matrix.mul_assoc Θinv B X, ← Matrix.mul_assoc B'ᴴ (Θinv * B) X, h2',
          ← Matrix.mul_assoc (B'ᴴ * B') Mtinv X]
      rw [h2, ← Matrix.mul_assoc (Ring.inverse (B'ᴴ * B')) (B'ᴴ * B') (Mtinv * X),
        Ring.inverse_mul_cancel _ hhB', Matrix.one_mul]
    rw [hgen']
    rw [← Matrix.mul_assoc Θ B' (Mtinv * (Ring.inverse (Bᴴ * B) * Bᴴ)), hB]
    rw [Matrix.mul_assoc B Mt (Mtinv * (Ring.inverse (Bᴴ * B) * Bᴴ)),
      ← Matrix.mul_assoc Mt Mtinv (Ring.inverse (Bᴴ * B) * Bᴴ), hMt, Matrix.one_mul]

theorem orthProj_conj_right {R : Type} [CommRing R] [StarRing R] {n : ℕ}
    (C C' : Matrix (Fin n ⊕ Fin n) (Fin n) R)
    (Θ Θinv : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (hC : Θ * C' = C) (hC' : Θinv * C = C')
    (hhC : IsUnit (Cᴴ * C)) (hhC' : IsUnit (C'ᴴ * C')) :
    (orthProj R C * (Θ * orthProj R C' * Θinv) = Θ * orthProj R C' * Θinv) ∧
    ((Θ * orthProj R C' * Θinv) * orthProj R C = orthProj R C) := by
  constructor
  · simp only [orthProj, Matrix.mul_assoc]
    have hgen : ∀ X : Matrix (Fin n) (Fin n ⊕ Fin n) R,
        Ring.inverse (Cᴴ * C) * (Cᴴ * (Θ * (C' * X))) = X := by
      intro X
      have h2' : Cᴴ * (Θ * C') = Cᴴ * C := by rw [hC]
      have h2 : Cᴴ * (Θ * (C' * X)) = (Cᴴ * C) * X := by
        rw [← Matrix.mul_assoc Θ C' X, ← Matrix.mul_assoc Cᴴ (Θ * C') X, h2']
      rw [h2, ← Matrix.mul_assoc (Ring.inverse (Cᴴ * C)) (Cᴴ * C) X,
        Ring.inverse_mul_cancel _ hhC, Matrix.one_mul]
    rw [hgen]
    rw [← Matrix.mul_assoc Θ C' (Ring.inverse (C'ᴴ * C') * (C'ᴴ * Θinv)), hC]
  · simp only [orthProj, Matrix.mul_assoc]
    have hgen' : ∀ X : Matrix (Fin n) (Fin n ⊕ Fin n) R,
        Ring.inverse (C'ᴴ * C') * (C'ᴴ * (Θinv * (C * X))) = X := by
      intro X
      have h2' : C'ᴴ * (Θinv * C) = C'ᴴ * C' := by rw [hC']
      have h2 : C'ᴴ * (Θinv * (C * X)) = (C'ᴴ * C') * X := by
        rw [← Matrix.mul_assoc Θinv C X, ← Matrix.mul_assoc C'ᴴ (Θinv * C) X, h2']
      rw [h2, ← Matrix.mul_assoc (Ring.inverse (C'ᴴ * C')) (C'ᴴ * C') X,
        Ring.inverse_mul_cancel _ hhC', Matrix.one_mul]
    rw [hgen']
    rw [← Matrix.mul_assoc Θ C' (Ring.inverse (Cᴴ * C) * Cᴴ), hC]

/-- The Murray-von Neumann core of the right-multiplication invariance of the clutched class. -/
theorem pairMat_mvN_conj {n : ℕ} (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (P Q P' Q' Θ Θi : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ))
    (hPQ : P.map (bdryRestrict X) = Q.map (bdryRestrict X))
    (hP'Q' : P'.map (bdryRestrict X) = Q'.map (bdryRestrict X))
    (hP' : P' * P' = P') (hQ' : Q' * Q' = Q')
    (hΘ : Θ * Θi = 1) (hΘi : Θi * Θ = 1)
    (h1 : P * (Θ * P' * Θi) = Θ * P' * Θi) (h2 : (Θ * P' * Θi) * P = P)
    (h3 : Q * (Θ * Q' * Θi) = Θ * Q' * Θi) (h4 : (Θ * Q' * Θi) * Q = Q) :
    ∃ a b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥(pullAlg2 X),
      b * a = pairMat X P' Q' hP'Q' ∧ a * b = pairMat X P Q hPQ := by
  have hA : (Θ * P').map (bdryRestrict X) = (Θ * Q').map (bdryRestrict X) := by
    simp only [Matrix.map_mul, hP'Q']
  have hB : (P' * Θi).map (bdryRestrict X) = (Q' * Θi).map (bdryRestrict X) := by
    simp only [Matrix.map_mul, hP'Q']
  have hR : (Θ * P' * Θi).map (bdryRestrict X) = (Θ * Q' * Θi).map (bdryRestrict X) := by
    simp only [Matrix.map_mul, hP'Q']
  set e' := pairMat X P' Q' hP'Q' with he'
  set e := pairMat X P Q hPQ with he
  set ρ := pairMat X (Θ * P' * Θi) (Θ * Q' * Θi) hR with hρ
  set A₁ := pairMat X (Θ * P') (Θ * Q') hA with hA₁
  set B₁ := pairMat X (P' * Θi) (Q' * Θi) hB with hB₁
  have hm0 : (P' * Θi) * (Θ * P') = P' * P' := by
    calc (P' * Θi) * (Θ * P') = ((P' * Θi) * Θ) * P' := (Matrix.mul_assoc (P' * Θi) Θ P').symm
      _ = (P' * (Θi * Θ)) * P' := by rw [Matrix.mul_assoc P' Θi Θ]
      _ = (P' * 1) * P' := by rw [hΘi]
      _ = P' * P' := by rw [Matrix.mul_one]
  have hm1 : (Q' * Θi) * (Θ * Q') = Q' * Q' := by
    calc (Q' * Θi) * (Θ * Q') = ((Q' * Θi) * Θ) * Q' := (Matrix.mul_assoc (Q' * Θi) Θ Q').symm
      _ = (Q' * (Θi * Θ)) * Q' := by rw [Matrix.mul_assoc Q' Θi Θ]
      _ = (Q' * 1) * Q' := by rw [hΘi]
      _ = Q' * Q' := by rw [Matrix.mul_one]
  have hBA : B₁ * A₁ = e' := by
    rw [hB₁, hA₁, he', pairMat_pull_mul hB hA]
    apply pairMat_pull_congr (hm0.trans hP') (hm1.trans hQ') <;>
      simp only [Matrix.map_mul, hB, hA, hP'Q']
  have hn0 : (Θ * P') * (P' * Θi) = Θ * P' * Θi := by
    calc (Θ * P') * (P' * Θi) = ((Θ * P') * P') * Θi := (Matrix.mul_assoc (Θ * P') P' Θi).symm
      _ = (Θ * (P' * P')) * Θi := by rw [Matrix.mul_assoc Θ P' P']
      _ = (Θ * P') * Θi := by rw [hP']
      _ = Θ * P' * Θi := rfl
  have hn1 : (Θ * Q') * (Q' * Θi) = Θ * Q' * Θi := by
    calc (Θ * Q') * (Q' * Θi) = ((Θ * Q') * Q') * Θi := (Matrix.mul_assoc (Θ * Q') Q' Θi).symm
      _ = (Θ * (Q' * Q')) * Θi := by rw [Matrix.mul_assoc Θ Q' Q']
      _ = (Θ * Q') * Θi := by rw [hQ']
      _ = Θ * Q' * Θi := rfl
  have hAB : A₁ * B₁ = ρ := by
    rw [hA₁, hB₁, hρ, pairMat_pull_mul hA hB]
    apply pairMat_pull_congr hn0 hn1 <;> simp only [Matrix.map_mul, hA, hB, hR]
  have hρe : ρ * e = e := by
    rw [hρ, he, pairMat_pull_mul hR hPQ]
    apply pairMat_pull_congr h2 h4 <;> simp only [Matrix.map_mul, hR, hPQ]
  have heρ : e * ρ = ρ := by
    rw [he, hρ, pairMat_pull_mul hPQ hR]
    apply pairMat_pull_congr h1 h3 <;> simp only [Matrix.map_mul, hPQ, hR]
  have he'e' : e' * e' = e' := by
    rw [he', pairMat_pull_mul hP'Q' hP'Q']
    apply pairMat_pull_congr hP' hQ' <;> simp only [Matrix.map_mul, hP'Q']
  refine ⟨ρ * A₁, B₁ * e, ?_, ?_⟩
  · rw [Matrix.mul_assoc B₁ e (ρ * A₁), ← Matrix.mul_assoc e ρ A₁, heρ,
      ← hAB, Matrix.mul_assoc A₁ B₁ A₁,
      ← Matrix.mul_assoc B₁ A₁ (B₁ * A₁), hBA, he'e']
  · show (ρ * A₁) * (B₁ * e) = e
    rw [Matrix.mul_assoc ρ A₁ (B₁ * e), ← Matrix.mul_assoc A₁ B₁ e, hAB, hρe, hρe]

/-- **Right multiplication by a unit with an invertible lift does not change the clutched class.**
This is the algebraic core of the multiplicativity of `κ`: with `F`, `G` lifts of `W`, `W⁻¹` and
`Mt` an *invertible* lift of `M`, the lifts `F * Mt`, `Mt⁻¹ * G` of `W * M`, `(W * M)⁻¹` give the
same class.

The two disc projections for `W * M` are conjugated (by `Θ = diag(Mt,1)`) into projections with the
same images as those of `W`; the gluing on the equator is compatible because the conjugation is
defined on the whole disc. -/
theorem clutchIdem_wmul_cls (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (W M : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (Mt : (Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))ˣ)
    (hMt : (Mt : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map (bdryRestrict X)
      = (M : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (F G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hF : F.map (bdryRestrict X) = (W : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (hG : G.map (bdryRestrict X)
      = ((W⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
          Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (hF' : (F * (Mt : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))).map (bdryRestrict X)
      = ((W * M : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
          Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (hG' : (((Mt⁻¹ : (Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))ˣ) :
        Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) * G).map (bdryRestrict X)
      = (((W * M)⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
          Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))) :
    cls (clutchIdem X n (W * M) (F * (Mt : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)))
          (((Mt⁻¹ : (Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))ˣ) :
            Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) * G) hF' hG')
      = cls (clutchIdem X n W F G hF hG) := by
  set Mtm : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
    (Mt : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) with hMtm
  set Mtmi : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
    ((Mt⁻¹ : (Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))ˣ) :
      Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) with hMtmi
  set Θ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) :=
    Matrix.fromBlocks Mtm 0 0 1 with hΘdef
  set Θi : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) :=
    Matrix.fromBlocks Mtmi 0 0 1 with hΘidef
  have hMtM : Mtm * Mtmi = 1 := by rw [hMtm, hMtmi]; exact Units.mul_inv Mt
  have hMtM' : Mtmi * Mtm = 1 := by rw [hMtm, hMtmi]; exact Units.inv_mul Mt
  have hΘ : Θ * Θi = 1 := by
    rw [hΘdef, hΘidef, Matrix.fromBlocks_multiply]
    simp [hMtM]
  have hΘi : Θi * Θ = 1 := by
    rw [hΘdef, hΘidef, Matrix.fromBlocks_multiply]
    simp [hMtM']
  have hf1 : Θ * graphB C(X × Ball ℂ, ℂ) (F * Mtm)
      = graphB C(X × Ball ℂ, ℂ) F * Mtm := by
    rw [hΘdef, graphB_eq_colBlock, blkDiag_mul_colBlock, graphB_eq_colBlock, colBlock_mul]
    simp
  have hf2 : Θ * recipB C(X × Ball ℂ, ℂ) (Mtmi * G)
      = recipB C(X × Ball ℂ, ℂ) G := by
    rw [hΘdef, recipB_eq_colBlock, blkDiag_mul_colBlock, recipB_eq_colBlock]
    congr 1
    rw [← Matrix.mul_assoc, hMtM, Matrix.one_mul]
  have hf3 : Θi * graphB C(X × Ball ℂ, ℂ) F
      = graphB C(X × Ball ℂ, ℂ) (F * Mtm) * Mtmi := by
    rw [hΘidef, graphB_eq_colBlock, blkDiag_mul_colBlock, graphB_eq_colBlock, colBlock_mul]
    congr 1
    · rw [Matrix.mul_one, Matrix.one_mul]
    · rw [Matrix.mul_assoc F Mtm Mtmi, hMtM, Matrix.mul_one]
  have hf4 : Θi * recipB C(X × Ball ℂ, ℂ) G
      = recipB C(X × Ball ℂ, ℂ) (Mtmi * G) := by
    rw [hΘidef, recipB_eq_colBlock, blkDiag_mul_colBlock, recipB_eq_colBlock]
  have hhB : IsUnit ((graphB C(X × Ball ℂ, ℂ) F)ᴴ * graphB C(X × Ball ℂ, ℂ) F) := by
    rw [(graphB_recipB_conjTranspose_mul_self C(X × Ball ℂ, ℂ) F G).1]
    exact isUnit_one_add_conjTranspose_mul F
  have hhB' : IsUnit ((graphB C(X × Ball ℂ, ℂ) (F * Mtm))ᴴ
      * graphB C(X × Ball ℂ, ℂ) (F * Mtm)) := by
    rw [(graphB_recipB_conjTranspose_mul_self C(X × Ball ℂ, ℂ) (F * Mtm) (Mtmi * G)).1]
    exact isUnit_one_add_conjTranspose_mul (F * Mtm)
  have hhC : IsUnit ((recipB C(X × Ball ℂ, ℂ) G)ᴴ * recipB C(X × Ball ℂ, ℂ) G) := by
    rw [(graphB_recipB_conjTranspose_mul_self C(X × Ball ℂ, ℂ) F G).2]
    exact isUnit_one_add_conjTranspose_mul G
  have hhC' : IsUnit ((recipB C(X × Ball ℂ, ℂ) (Mtmi * G))ᴴ
      * recipB C(X × Ball ℂ, ℂ) (Mtmi * G)) := by
    rw [(graphB_recipB_conjTranspose_mul_self C(X × Ball ℂ, ℂ) (F * Mtm) (Mtmi * G)).2]
    exact isUnit_one_add_conjTranspose_mul (Mtmi * G)
  have hL := orthProj_conj_left (graphB C(X × Ball ℂ, ℂ) F)
    (graphB C(X × Ball ℂ, ℂ) (F * Mtm)) Mtm Mtmi Θ Θi hf1 hf3 hMtM hhB hhB'
  have hR := orthProj_conj_right (recipB C(X × Ball ℂ, ℂ) G)
    (recipB C(X × Ball ℂ, ℂ) (Mtmi * G)) Θ Θi hf2 hf4 hhC hhC'
  have hPQ : (graphProj C(X × Ball ℂ, ℂ) F).map (bdryRestrict X)
      = (recipProj C(X × Ball ℂ, ℂ) G).map (bdryRestrict X) :=
    clutch_agree X n W F G hF hG
  have hP'Q' : (graphProj C(X × Ball ℂ, ℂ) (F * Mtm)).map (bdryRestrict X)
      = (recipProj C(X × Ball ℂ, ℂ) (Mtmi * G)).map (bdryRestrict X) :=
    clutch_agree X n (W * M) (F * Mtm) (Mtmi * G) hF' hG'
  have hidemP' : graphProj C(X × Ball ℂ, ℂ) (F * Mtm)
      * graphProj C(X × Ball ℂ, ℂ) (F * Mtm)
      = graphProj C(X × Ball ℂ, ℂ) (F * Mtm) := graphProj_isIdem X (F * Mtm)
  have hidemQ' : recipProj C(X × Ball ℂ, ℂ) (Mtmi * G)
      * recipProj C(X × Ball ℂ, ℂ) (Mtmi * G)
      = recipProj C(X × Ball ℂ, ℂ) (Mtmi * G) := recipProj_isIdem X (Mtmi * G)
  obtain ⟨a, b, hba, hab⟩ := pairMat_mvN_conj X
    (graphProj C(X × Ball ℂ, ℂ) F) (recipProj C(X × Ball ℂ, ℂ) G)
    (graphProj C(X × Ball ℂ, ℂ) (F * Mtm)) (recipProj C(X × Ball ℂ, ℂ) (Mtmi * G))
    Θ Θi hPQ hP'Q' hidemP' hidemQ' hΘ hΘi
    (by simpa only [graphProj, recipProj] using hL.1)
    (by simpa only [graphProj, recipProj] using hL.2)
    (by simpa only [graphProj, recipProj] using hR.1)
    (by simpa only [graphProj, recipProj] using hR.2)
  refine cls_eq_of_mvn (clutchIdem_isIdem X n (W * M) (F * Mtm) (Mtmi * G) hF' hG')
    (clutchIdem_isIdem X n W F G hF hG) ?_
  refine ⟨a.submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
    b.submatrix finSumFinEquiv.symm finSumFinEquiv.symm, ?_, ?_⟩
  · show (b.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
        * (a.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) = _
    rw [Matrix.submatrix_mul_equiv b a _ _ _, hba]
    rfl
  · show (a.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
        * (b.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) = _
    rw [Matrix.submatrix_mul_equiv a b _ _ _, hab]
    rfl

/-- **`κ` is unchanged by right multiplication with a unit that has an invertible lift to the disc.**
This is the multiplicativity input for `κ`: a unit of the circle algebra which is the boundary value
of an *invertible* matrix over the disc has trivial clutching. -/
theorem kappa_wmul_eq (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (W M : (Matrix (Fin n) (Fin n) Circ[X])ˣ)
    (Mt : (Matrix (Fin n) (Fin n) Disc[X])ˣ)
    (hMt : (Mt : Matrix (Fin n) (Fin n) Disc[X]).map (bdryRestrict X)
      = (M : Matrix (Fin n) (Fin n) Circ[X])) :
    kappa X n (W * M) = kappa X n W := by
  have hMtinv : (((Mt⁻¹ : (Matrix (Fin n) (Fin n) Disc[X])ˣ) :
        Matrix (Fin n) (Fin n) Disc[X]).map (bdryRestrict X))
      = (((M⁻¹ : (Matrix (Fin n) (Fin n) Circ[X])ˣ) :
        Matrix (Fin n) (Fin n) Circ[X])) := by
    have hmap : Units.map ((RingHom.mapMatrix (bdryRestrict X) :
        Matrix (Fin n) (Fin n) Disc[X] →+* Matrix (Fin n) (Fin n) Circ[X])).toMonoidHom Mt
        = M := by
      refine Units.ext ?_
      show (RingHom.mapMatrix (bdryRestrict X)) (Mt : Matrix (Fin n) (Fin n) Disc[X])
        = (M : Matrix (Fin n) (Fin n) Circ[X])
      simpa using hMt
    have h2 : (Units.map ((RingHom.mapMatrix (bdryRestrict X) :
        Matrix (Fin n) (Fin n) Disc[X] →+* Matrix (Fin n) (Fin n) Circ[X])).toMonoidHom)
        (Mt⁻¹) = M⁻¹ := by
      rw [map_inv, hmap]
    have h3 := congrArg (fun u : (Matrix (Fin n) (Fin n) Circ[X])ˣ =>
      (u : Matrix (Fin n) (Fin n) Circ[X])) h2
    exact h3
  have hbF1 : ((liftOf X (W : Matrix (Fin n) (Fin n) Circ[X])
        * (Mt : Matrix (Fin n) (Fin n) Disc[X])).map (bdryRestrict X))
      = ((W * M : (Matrix (Fin n) (Fin n) Circ[X])ˣ) : Matrix (Fin n) (Fin n) Circ[X]) := by
    rw [Matrix.map_mul, liftOf_spec, hMt, Units.val_mul]
  have hbG1 : ((((Mt⁻¹ : (Matrix (Fin n) (Fin n) Disc[X])ˣ) :
        Matrix (Fin n) (Fin n) Disc[X])
        * liftOf X ((W⁻¹ : (Matrix (Fin n) (Fin n) Circ[X])ˣ) :
            Matrix (Fin n) (Fin n) Circ[X])).map (bdryRestrict X))
      = (((W * M)⁻¹ : (Matrix (Fin n) (Fin n) Circ[X])ˣ) : Matrix (Fin n) (Fin n) Circ[X]) := by
    rw [Matrix.map_mul, hMtinv, liftOf_spec, ← Units.val_mul, _root_.mul_inv_rev]
  have hmid : cls (clutchIdem X n (W * M)
        ((liftOf X (W : Matrix (Fin n) (Fin n) Circ[X]))
          * (Mt : Matrix (Fin n) (Fin n) Disc[X]))
        (((Mt⁻¹ : (Matrix (Fin n) (Fin n) Disc[X])ˣ) :
            Matrix (Fin n) (Fin n) Disc[X])
          * liftOf X ((W⁻¹ : (Matrix (Fin n) (Fin n) Circ[X])ˣ) :
              Matrix (Fin n) (Fin n) Circ[X]))
        hbF1 hbG1)
      = cls (clutchIdem X n W
        (liftOf X (W : Matrix (Fin n) (Fin n) Circ[X]))
        (liftOf X ((W⁻¹ : (Matrix (Fin n) (Fin n) Circ[X])ˣ) :
          Matrix (Fin n) (Fin n) Circ[X]))
        (liftOf_spec X (W : Matrix (Fin n) (Fin n) Circ[X]))
        (liftOf_spec X ((W⁻¹ : (Matrix (Fin n) (Fin n) Circ[X])ˣ) :
          Matrix (Fin n) (Fin n) Circ[X]))) :=
    clutchIdem_wmul_cls X n W M Mt hMt
      (liftOf X (W : Matrix (Fin n) (Fin n) Circ[X]))
      (liftOf X ((W⁻¹ : (Matrix (Fin n) (Fin n) Circ[X])ˣ) :
        Matrix (Fin n) (Fin n) Circ[X]))
      (liftOf_spec X (W : Matrix (Fin n) (Fin n) Circ[X]))
      (liftOf_spec X ((W⁻¹ : (Matrix (Fin n) (Fin n) Circ[X])ˣ) :
        Matrix (Fin n) (Fin n) Circ[X])) hbF1 hbG1
  refine congrArg (k0Glue X).symm ?_
  exact (clutchIdem_cls_indep X n (W * M)
      (liftOf X ((W * M : (Matrix (Fin n) (Fin n) Circ[X])ˣ) :
        Matrix (Fin n) (Fin n) Circ[X]))
      (liftOf X (((W * M)⁻¹ : (Matrix (Fin n) (Fin n) Circ[X])ˣ) :
        Matrix (Fin n) (Fin n) Circ[X]))
      _ _ (liftOf_spec X ((W * M : (Matrix (Fin n) (Fin n) Circ[X])ˣ) :
        Matrix (Fin n) (Fin n) Circ[X]))
      (liftOf_spec X (((W * M)⁻¹ : (Matrix (Fin n) (Fin n) Circ[X])ˣ) :
        Matrix (Fin n) (Fin n) Circ[X]))
      hbF1 hbG1).trans hmid

/-! ## Elementary matrices and Tietze lifts -/

/-- A Tietze lift of a function on the circle to the disc. -/
def slift (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (a : Circ[X]) : Disc[X] :=
  (Work.KT.ExtGen.bdryRestrict_surjective X a).choose

lemma slift_spec (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (a : Circ[X]) : bdryRestrict X (slift X a) = a :=
  (Work.KT.ExtGen.bdryRestrict_surjective X a).choose_spec

/-- The elementary invertible matrix `1 + single i j a` (for `i ≠ j`). -/
def elemUnit (R : Type) [Ring R] {m : ℕ} (i j : Fin m) (hij : i ≠ j) (a : R) :
    (Matrix (Fin m) (Fin m) R)ˣ where
  val := 1 + Matrix.single i j a
  inv := 1 - Matrix.single i j a
  val_inv := by
    have hs : Matrix.single i j a * Matrix.single i j a = 0 :=
      Matrix.single_mul_single_of_ne a i j i (Ne.symm hij) a
    simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hs]
    abel
  inv_val := by
    have hs : Matrix.single i j a * Matrix.single i j a = 0 :=
      Matrix.single_mul_single_of_ne a i j i (Ne.symm hij) a
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, hs]
    abel

lemma elemUnit_val_map {R S : Type} [Ring R] [Ring S] (φ : R →+* S) {m : ℕ}
    (i j : Fin m) (hij : i ≠ j) (a : R) :
    ((elemUnit R i j hij a : Matrix (Fin m) (Fin m) R).map φ)
      = (elemUnit S i j hij (φ a) : Matrix (Fin m) (Fin m) S) := by
  show (φ.mapMatrix) (1 + Matrix.single i j a : Matrix (Fin m) (Fin m) R)
      = (1 + Matrix.single i j (φ a) : Matrix (Fin m) (Fin m) S)
  rw [map_add, map_one]
  congr 1
  rw [show (φ.mapMatrix) (Matrix.single i j a) = (Matrix.single i j a).map ⇑φ from rfl,
    Matrix.map_single]

/-- **A product of elementary matrices has an invertible lift to the disc.** -/
lemma exists_lift_list (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (m : ℕ) : ∀ (e : List (Matrix (Fin m) (Fin m) Circ[X])),
      (∀ t ∈ e, ∃ i j a, i ≠ j ∧ t = 1 + Matrix.single i j a) →
      ∃ Mt : (Matrix (Fin m) (Fin m) Disc[X])ˣ,
        (Mt : Matrix (Fin m) (Fin m) Disc[X]).map (bdryRestrict X) = e.prod := by
  intro e
  induction e with
  | nil => intro _; exact ⟨1, by simp⟩
  | cons t rest ih =>
    intro h
    obtain ⟨i, j, a, hij, ht⟩ := h t List.mem_cons_self
    obtain ⟨Mtr, hMtr⟩ := ih (fun s hs => h s (List.mem_cons_of_mem t hs))
    refine ⟨elemUnit Disc[X] i j hij (slift X a) * Mtr, ?_⟩
    rw [Units.val_mul, Matrix.map_mul, elemUnit_val_map, slift_spec, hMtr, List.prod_cons, ht]
    rfl

/-- The block-diagonal unit `diag(a,b)`. -/
private def blkUnit {R : Type} [Ring R] {m₁ m₂ : ℕ}
    (a : (Matrix (Fin m₁) (Fin m₁) R)ˣ) (b : (Matrix (Fin m₂) (Fin m₂) R)ˣ) :
    (Matrix (Fin m₁ ⊕ Fin m₂) (Fin m₁ ⊕ Fin m₂) R)ˣ where
  val := Matrix.fromBlocks (a : Matrix (Fin m₁) (Fin m₁) R) 0 0
    (b : Matrix (Fin m₂) (Fin m₂) R)
  inv := Matrix.fromBlocks ((a⁻¹ : (Matrix (Fin m₁) (Fin m₁) R)ˣ) : Matrix (Fin m₁) (Fin m₁) R)
    0 0 ((b⁻¹ : (Matrix (Fin m₂) (Fin m₂) R)ˣ) : Matrix (Fin m₂) (Fin m₂) R)
  val_inv := by
    rw [Matrix.fromBlocks_multiply]
    simp
  inv_val := by
    rw [Matrix.fromBlocks_multiply]
    simp

lemma reindex_finSum_mul' {R : Type} [Ring R] {m : ℕ}
    (A B : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv A
        * Matrix.reindex finSumFinEquiv finSumFinEquiv B
      = Matrix.reindex finSumFinEquiv finSumFinEquiv (A * B) :=
  Work.KT.reindex_finSum_mul A B

/-! ## The theorem -/

theorem kappa_mul (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (u v : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (huv : (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) *
        (v : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = (v : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) *
        (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))) :
    Work.KT.Fund.kappa X n (u * v) = Work.KT.Fund.kappa X n u + Work.KT.Fund.kappa X n v
      - Work.KT.cls (Work.KT.Mat.one C(X × S2, ℂ) n) := by
  set Uv : (Matrix (Fin (n + n)) (Fin (n + n)) Circ[X])ˣ :=
    Units.map (Matrix.reindexRingEquiv Circ[X] finSumFinEquiv).toMonoidHom (blkUnit u v) with hUvdef
  set Uw : (Matrix (Fin (n + n)) (Fin (n + n)) Circ[X])ˣ :=
    Units.map (Matrix.reindexRingEquiv Circ[X] finSumFinEquiv).toMonoidHom
      (blkUnit (u * v) (1 : (Matrix (Fin n) (Fin n) Circ[X])ˣ)) with hUwdef
  set E : (Matrix (Fin (n + n)) (Fin (n + n)) Circ[X])ˣ :=
    Units.map (Matrix.reindexRingEquiv Circ[X] finSumFinEquiv).toMonoidHom
      (blkUnit (v⁻¹) v) with hEdef
  have hUvval : (Uv : Matrix (Fin (n + n)) (Fin (n + n)) Circ[X])
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (u : Matrix (Fin n) (Fin n) Circ[X]) 0 0
            (v : Matrix (Fin n) (Fin n) Circ[X])) := rfl
  have hUwval : (Uw : Matrix (Fin (n + n)) (Fin (n + n)) Circ[X])
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks ((u * v : (Matrix (Fin n) (Fin n) Circ[X])ˣ) :
            Matrix (Fin n) (Fin n) Circ[X]) 0 0
              (1 : Matrix (Fin n) (Fin n) Circ[X])) := rfl
  have hEval : (E : Matrix (Fin (n + n)) (Fin (n + n)) Circ[X])
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks ((v⁻¹ : (Matrix (Fin n) (Fin n) Circ[X])ˣ) :
            Matrix (Fin n) (Fin n) Circ[X]) 0 0 (v : Matrix (Fin n) (Fin n) Circ[X])) := rfl
  have hUvEq : Uv = Uw * E := by
    refine Units.ext ?_
    rw [hUvdef, hUwdef, hEdef, Units.val_mul, hUvval, hUwval, hEval, reindex_finSum_mul']
    congr 1
    rw [Matrix.fromBlocks_multiply]
    ext i j
    cases i <;> cases j <;> simp [Units.val_mul, Units.mul_inv]
  obtain ⟨e, he, heprod⟩ := Work.KT.whitehead_diag
    ((v⁻¹ : (Matrix (Fin n) (Fin n) Circ[X])ˣ) : Matrix (Fin n) (Fin n) Circ[X])
    (v : Matrix (Fin n) (Fin n) Circ[X]) (Units.mul_inv v) (Units.inv_mul v)
  have heE : e.prod = (E : Matrix (Fin (n + n)) (Fin (n + n)) Circ[X]) := by
    rw [heprod]
    exact hEval.symm
  obtain ⟨Mt, hMt⟩ := exists_lift_list X (n + n) e he
  rw [heE] at hMt
  have hstep : kappa X (n + n) (Uw * E) = kappa X (n + n) Uw :=
    kappa_wmul_eq X (n + n) Uw E Mt hMt
  have h1 : kappa X (n + n) Uv = kappa X n u + kappa X n v :=
    kappa_add_blocks X n n Uv u v hUvval
  have h2 : kappa X (n + n) Uw = kappa X n (u * v) + kappa X n 1 :=
    kappa_add_blocks X n n Uw (u * v) 1 hUwval
  have h3 : kappa X n 1 = cls (Mat.one C(X × S2, ℂ) n) := kappa_one_alt X n
  have key : kappa X n u + kappa X n v
      = kappa X n (u * v) + cls (Mat.one C(X × S2, ℂ) n) := by
    rw [← h1, hUvEq, hstep, h2, h3]
  exact (eq_sub_iff_add_eq).mpr key.symm

end

end Work.KT.Fund
