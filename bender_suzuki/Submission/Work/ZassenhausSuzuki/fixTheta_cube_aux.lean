import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.SzTildeDefs
import Submission.Work.ZassenhausSuzuki.szTildeAux
import Submission.Work.ZassenhausSuzuki.szTilde_comm_of_fix
import Submission.Work.ZassenhausSuzuki.szTilde_sq
import Submission.Work.ZassenhausSuzuki.SzAField
import Submission.Work.ZassenhausSuzuki.torusLambda_surjective_of_split
import Submission.Work.ZassenhausSuzuki.szTilde_conj
import Submission.Work.ZassenhausSuzuki.canon_relations

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Auxiliaries for BG 5.14 (a) in the split rank-one Zassenhaus configuration

Contains the coordinate description of the Suzuki reflection `∼ = szTilde hsplit` on the
*central* involutions of the root group and the resulting coordinates of the central element
`c := (∼a₁)⁻¹(∼a₀)(∼(a₀a₁))⁻¹` of BG's Lemma 5.14 (a).

* `szTilde_zc_b` — for `b ≠ 0` the second coordinate of `e (∼ (zc e b))` is `κ · b` where
  `κ := (e (∼ (zc e 1))).b`.  (First coordinate: `ν · θ ν = b`, `szTilde_coord_sq`.)
* `szTilde_zc_base` — `e (∼ (zc e 1)) = ⟨1, κ⟩`.
* `e_tilde_zc_fix` — for `θ λ = λ`, `λ ≠ 0,1`:
  `e (∼ (zc e (λ²))) = ⟨λ, κ λ²⟩` and `e (∼ (zc e (1 + λ²))) = ⟨1 + λ, κ (1 + λ²)⟩`.
* `e_c_mul` — the `e`-coordinates of `c := (∼a₁)⁻¹(∼a₀)(∼(a₀a₁))⁻¹` are `⟨0, λ² + λ⟩`
  (`a₀ = zc e 1`, `a₁ = zc e λ²`), so `c` is a non-trivial central involution.
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- **The `e`-coordinates of `∼` on the central involutions.**
For `b ≠ 0` the second coordinate of `e (∼ (zc e b))` is the constant
`κ := (e (∼ (zc e 1))).b` times `b`: this is the `D`-equivariance of `∼` (`szTilde_conj`)
combined with the surjectivity of `λ ↦ λ·θλ` on `Kˣ` (`units_mul_map_surjective`), the
`D`-action on the centre being `h_λ (0,b) = (0, λ·θλ·b)`. -/
theorem szTilde_zc_b (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ))
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {b : GaloisField 2 m} (hb : b ≠ 0) :
    (e (Work.ZassenhausSuzuki.szTilde hsplit (Work.ZassenhausSuzuki.zc e b))).b
      = (e (Work.ZassenhausSuzuki.szTilde hsplit (Work.ZassenhausSuzuki.zc e 1))).b * b := by
  classical
  have h2 : IsPGroup 2 Q := isPGroup_two_of_mulEquiv θ e
  obtain ⟨lam, hlam⟩ := units_mul_map_surjective θ hθodd (Units.mk0 b hb)
  have hlamK : (lam : GaloisField 2 m) * θ (lam : GaloisField 2 m) = b := by
    have h := congrArg (fun u : (GaloisField 2 m)ˣ => (u : GaloisField 2 m)) hlam
    simpa [Units.val_mul] using h
  obtain ⟨d, hd, hact⟩ :=
    torusLambda_surjective_of_split hsplit hzass h2 (θ := θ) htorus lam
  have hconj : ((Work.ZassenhausSuzuki.zc e b : Q) : G)
      = d * ((Work.ZassenhausSuzuki.zc e 1 : Q) : G) * d⁻¹ := by
    have h := hact (Work.ZassenhausSuzuki.zc e 1)
    rw [Work.ZassenhausSuzuki.zc_coe] at h
    have h1 : Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m)
        (⟨0, 1⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ)
        = (⟨0, b⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) := by
      ext <;> simp [Work.ZassenhausSuzuki.SzA.hLam_a, Work.ZassenhausSuzuki.SzA.hLam_b, hlamK]
    rw [h1] at h
    simpa [Work.ZassenhausSuzuki.zc] using h
  have hconj2 : ((Work.ZassenhausSuzuki.szTilde hsplit
        (Work.ZassenhausSuzuki.zc e b) : Q) : G)
      = d * ((Work.ZassenhausSuzuki.szTilde hsplit
        (Work.ZassenhausSuzuki.zc e 1) : Q) : G) * d⁻¹ :=
    szTilde_conj hsplit hzass h2 hd hconj
  have hy_eq : e.symm (Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m)
        (e (Work.ZassenhausSuzuki.szTilde hsplit (Work.ZassenhausSuzuki.zc e 1))))
      = Work.ZassenhausSuzuki.szTilde hsplit (Work.ZassenhausSuzuki.zc e b) :=
    Subtype.ext ((hact (Work.ZassenhausSuzuki.szTilde hsplit
      (Work.ZassenhausSuzuki.zc e 1))).trans hconj2.symm)
  have hkey : e (Work.ZassenhausSuzuki.szTilde hsplit (Work.ZassenhausSuzuki.zc e b))
      = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m)
          (e (Work.ZassenhausSuzuki.szTilde hsplit (Work.ZassenhausSuzuki.zc e 1))) := by
    rw [← hy_eq, MulEquiv.apply_symm_apply]
  have hκ : e (Work.ZassenhausSuzuki.szTilde hsplit (Work.ZassenhausSuzuki.zc e 1))
      = (⟨1, (e (Work.ZassenhausSuzuki.szTilde hsplit
            (Work.ZassenhausSuzuki.zc e 1))).b⟩
          : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) := by
    have hcoord := szTilde_coord_sq hsplit hzass hθ1 hθodd htorus
      (a := Work.ZassenhausSuzuki.zc e 1) (b := 1)
      (by rw [Work.ZassenhausSuzuki.zc_coe]) one_ne_zero
    have hone : (e (Work.ZassenhausSuzuki.szTilde hsplit
        (Work.ZassenhausSuzuki.zc e 1))).a = 1 := by
      refine eq_one_of_mul_map_eq_one θ hθodd ?_ hcoord
      intro h0
      rw [h0, zero_mul] at hcoord
      exact one_ne_zero hcoord.symm
    exact Work.ZassenhausSuzuki.SzA.ext hone rfl
  rw [hkey, hκ]
  simp only [Work.ZassenhausSuzuki.SzA.hLam_b]
  rw [hlamK, mul_comm]

/-- `e (∼ (zc e 1)) = ⟨1, κ⟩` where `κ = (e (∼ (zc e 1))).b`. -/
theorem szTilde_zc_base (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ))
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x)) :
    e (Work.ZassenhausSuzuki.szTilde hsplit (Work.ZassenhausSuzuki.zc e 1))
      = (⟨1, (e (Work.ZassenhausSuzuki.szTilde hsplit
            (Work.ZassenhausSuzuki.zc e 1))).b⟩
          : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) := by
  have hcoord := szTilde_coord_sq hsplit hzass hθ1 hθodd htorus
    (a := Work.ZassenhausSuzuki.zc e 1) (b := 1)
    (by rw [Work.ZassenhausSuzuki.zc_coe]) one_ne_zero
  have hone : (e (Work.ZassenhausSuzuki.szTilde hsplit
      (Work.ZassenhausSuzuki.zc e 1))).a = 1 := by
    refine eq_one_of_mul_map_eq_one θ hθodd ?_ hcoord
    intro h0
    rw [h0, zero_mul] at hcoord
    exact one_ne_zero hcoord.symm
  exact Work.ZassenhausSuzuki.SzA.ext hone rfl

/-- **The coordinates of `∼` at the `θ`-fixed central involutions.**  Let `θ λ = λ` with
`λ ≠ 0,1`, and put `κ := (e (∼ (zc e 1))).b`.  Then
`e (∼ (zc e (λ²))) = ⟨λ, κ λ²⟩` and `e (∼ (zc e (1 + λ²))) = ⟨1 + λ, κ (1 + λ²)⟩`. -/
theorem e_tilde_zc_fix (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ))
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {lam : GaloisField 2 m} (hfix : θ lam = lam) (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    e (Work.ZassenhausSuzuki.szTilde hsplit (Work.ZassenhausSuzuki.zc e (lam ^ 2)))
        = (⟨lam, (e (Work.ZassenhausSuzuki.szTilde hsplit
              (Work.ZassenhausSuzuki.zc e 1))).b * lam ^ 2⟩
            : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ)
      ∧ e (Work.ZassenhausSuzuki.szTilde hsplit
            (Work.ZassenhausSuzuki.zc e (1 + lam ^ 2)))
          = (⟨1 + lam, (e (Work.ZassenhausSuzuki.szTilde hsplit
                (Work.ZassenhausSuzuki.zc e 1))).b * (1 + lam ^ 2)⟩
              : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) := by
  have h2 : IsPGroup 2 Q := isPGroup_two_of_mulEquiv θ e
  have hclam : (2 : GaloisField 2 m) = 0 := CharP.cast_eq_zero (R := GaloisField 2 m) 2
  have hlam2 : lam ^ 2 ≠ 0 := pow_ne_zero 2 h0
  have h1l : 1 + lam ≠ 0 := by
    intro h
    exact h1 (by linear_combination h - hclam)
  have h1l2 : (1 + lam ^ 2 : GaloisField 2 m) ≠ 0 := by
    have hsq : (1 + lam) * (1 + lam) = 1 + lam ^ 2 := by
      ring_nf
      simp only [hclam, mul_zero, add_zero]
    rw [← hsq]
    exact mul_ne_zero h1l h1l
  constructor
  · -- first conjunct
    have hb : (e (Work.ZassenhausSuzuki.szTilde hsplit
        (Work.ZassenhausSuzuki.zc e (lam ^ 2)))).b
        = (e (Work.ZassenhausSuzuki.szTilde hsplit
            (Work.ZassenhausSuzuki.zc e 1))).b * lam ^ 2 :=
      szTilde_zc_b hsplit hzass hθ1 hθodd htorus hlam2
    have hcoord := szTilde_coord_sq hsplit hzass hθ1 hθodd htorus
      (a := Work.ZassenhausSuzuki.zc e (lam ^ 2)) (b := lam ^ 2)
      (by rw [Work.ZassenhausSuzuki.zc_coe]) hlam2
    have ha : (e (Work.ZassenhausSuzuki.szTilde hsplit
        (Work.ZassenhausSuzuki.zc e (lam ^ 2)))).a = lam := by
      refine mul_theta_injective θ hθodd ?_
      have hstep : (e (Work.ZassenhausSuzuki.szTilde hsplit
            (Work.ZassenhausSuzuki.zc e (lam ^ 2)))).a
            * θ ((e (Work.ZassenhausSuzuki.szTilde hsplit
              (Work.ZassenhausSuzuki.zc e (lam ^ 2)))).a) = lam * θ lam :=
        hcoord.trans (by rw [hfix, pow_two])
      simpa only [] using hstep
    exact Work.ZassenhausSuzuki.SzA.ext ha hb
  · -- second conjunct
    have hb : (e (Work.ZassenhausSuzuki.szTilde hsplit
        (Work.ZassenhausSuzuki.zc e (1 + lam ^ 2)))).b
        = (e (Work.ZassenhausSuzuki.szTilde hsplit
            (Work.ZassenhausSuzuki.zc e 1))).b * (1 + lam ^ 2) :=
      szTilde_zc_b hsplit hzass hθ1 hθodd htorus h1l2
    have hcoord := szTilde_coord_sq hsplit hzass hθ1 hθodd htorus
      (a := Work.ZassenhausSuzuki.zc e (1 + lam ^ 2)) (b := 1 + lam ^ 2)
      (by rw [Work.ZassenhausSuzuki.zc_coe]) h1l2
    have hsq : (1 + lam) * (1 + lam) = 1 + lam ^ 2 := by
      ring_nf
      simp only [hclam, mul_zero, add_zero]
    have ha : (e (Work.ZassenhausSuzuki.szTilde hsplit
        (Work.ZassenhausSuzuki.zc e (1 + lam ^ 2)))).a = 1 + lam := by
      refine mul_theta_injective θ hθodd ?_
      have hstep : (e (Work.ZassenhausSuzuki.szTilde hsplit
            (Work.ZassenhausSuzuki.zc e (1 + lam ^ 2)))).a
            * θ ((e (Work.ZassenhausSuzuki.szTilde hsplit
              (Work.ZassenhausSuzuki.zc e (1 + lam ^ 2)))).a)
            = (1 + lam) * θ (1 + lam) :=
        hcoord.trans (by rw [map_add, map_one, hfix]; exact hsq.symm)
      simpa only [] using hstep
    exact Work.ZassenhausSuzuki.SzA.ext ha hb

/-- **The coordinates of BG's central element `c`.**  For `θ λ = λ`, `λ ≠ 0,1`, with
`a₀ := zc e 1`, `a₁ := zc e (λ²)` and `c := (∼a₁)⁻¹ · (∼a₀) · (∼(a₀·a₁))⁻¹`, one has
`e c = ⟨0, λ² + λ⟩`; in particular `c ≠ 1`. -/
theorem e_c_mul (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ))
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {lam : GaloisField 2 m} (hfix : θ lam = lam) (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    e ((Work.ZassenhausSuzuki.szTilde hsplit
          (Work.ZassenhausSuzuki.zc e (lam ^ 2)))⁻¹
        * Work.ZassenhausSuzuki.szTilde hsplit (Work.ZassenhausSuzuki.zc e 1)
        * (Work.ZassenhausSuzuki.szTilde hsplit
            (Work.ZassenhausSuzuki.zc e (1 + lam ^ 2)))⁻¹)
      = (⟨0, lam ^ 2 + lam⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) := by
  have h2 : IsPGroup 2 Q := isPGroup_two_of_mulEquiv θ e
  obtain ⟨h1', h2'⟩ := e_tilde_zc_fix hsplit hzass hθ1 hθodd htorus hfix h0 h1
  have hbase := szTilde_zc_base hsplit hzass hθ1 hθodd htorus
  -- the product `a₀ · a₁ = zc e (1 + λ²)`
  have hmul : Work.ZassenhausSuzuki.zc e 1 * Work.ZassenhausSuzuki.zc e (lam ^ 2)
      = Work.ZassenhausSuzuki.zc e (1 + lam ^ 2) := by
    apply e.injective
    ext <;> simp [Work.ZassenhausSuzuki.zc_coe, Work.ZassenhausSuzuki.SzA.mul_a,
      Work.ZassenhausSuzuki.SzA.mul_b]
  rw [map_mul, map_mul, map_inv, map_inv, h1', hbase, h2']
  have hc : (2 : GaloisField 2 m) = 0 := CharP.cast_eq_zero (R := GaloisField 2 m) 2
  have h3 : (3 : GaloisField 2 m) = 1 := by
    rw [show (3 : GaloisField 2 m) = 2 + 1 by norm_num, hc, zero_add]
  have h5 : (5 : GaloisField 2 m) = 1 := by
    rw [show (5 : GaloisField 2 m) = 4 + 1 by norm_num,
      show (4 : GaloisField 2 m) = 2 * 2 by norm_num, hc, mul_zero, zero_add]
  ext <;>
    simp only [Work.ZassenhausSuzuki.SzA.mul_a, Work.ZassenhausSuzuki.SzA.mul_b,
      Work.ZassenhausSuzuki.SzA.inv_a, Work.ZassenhausSuzuki.SzA.inv_b,
      Work.ZassenhausSuzuki.SzA.one_a, Work.ZassenhausSuzuki.SzA.one_b,
      map_add, map_one, map_neg, hfix, CharTwo.neg_eq,
      hc, h3, h5, mul_zero, zero_mul, mul_one, add_zero, zero_add] <;>
    ring_nf <;>
    simp only [hc, h3, h5, mul_zero, zero_mul, mul_one, add_zero, zero_add,
      neg_zero, CharTwo.neg_eq]

/-- **`∼` is injective on the central involutions `Z(Q)^#`** (the `a`-coordinate of `e (∼ z)` is
the `(1+θ)`-root of the `b`-coordinate of `z`, `szTilde_coord_sq`). -/
theorem szTilde_zc_injective (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ))
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {b b' : GaloisField 2 m} (hb : b ≠ 0) (hb' : b' ≠ 0)
    (h : Work.ZassenhausSuzuki.szTilde hsplit (Work.ZassenhausSuzuki.zc e b)
      = Work.ZassenhausSuzuki.szTilde hsplit (Work.ZassenhausSuzuki.zc e b')) :
    b = b' := by
  have h1 := szTilde_coord_sq hsplit hzass hθ1 hθodd htorus
    (a := Work.ZassenhausSuzuki.zc e b) (b := b)
    (by rw [Work.ZassenhausSuzuki.zc_coe]) hb
  have h2 := szTilde_coord_sq hsplit hzass hθ1 hθodd htorus
    (a := Work.ZassenhausSuzuki.zc e b') (b := b')
    (by rw [Work.ZassenhausSuzuki.zc_coe]) hb'
  rw [h] at h1
  exact h1.symm.trans h2

end Work.ZassenhausSuzuki
