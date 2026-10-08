import Mathlib
import Submission.Work.ZassenhausSuzuki.TitsAux
import Submission.Work.ZassenhausSuzuki.frel_torus_inv
import Submission.Work.RankOneUniqueness.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ZassenhausSuzuki

open Submission.Blueprint

/-! ## Coordinate lemmas in `A(K,θ)` (characteristic two) -/

section Coords

variable {K : Type*} [Field K] [CharP K 2]

private lemma SzA_inv_one_one (θ : K ≃+* K) :
    (⟨1, 1⟩ : SzA K θ)⁻¹ = ⟨1, 0⟩ := by
  ext <;> simp [SzA.inv_a, SzA.inv_b, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private lemma SzA_one_zero_mul (θ : K ≃+* K) (c : K) :
    (⟨1, 0⟩ : SzA K θ) * ⟨c, c * θ c⟩ = ⟨1 + c, θ c * (1 + c)⟩ := by
  ext <;> simp only [SzA.mul_a, SzA.mul_b, SzA.one_a, SzA.one_b, zero_mul, zero_add] <;> ring

private lemma SzA_hLam_zero_one (θ : K ≃+* K) (c : K) :
    SzA.hLam θ c (⟨0, 1⟩ : SzA K θ) = ⟨0, c * θ c⟩ := by
  ext <;> simp [SzA.hLam]

private lemma SzA_hLam_one_one (θ : K ≃+* K) (c : K) :
    SzA.hLam θ c (⟨1, 1⟩ : SzA K θ) = ⟨c, c * θ c⟩ := by
  ext <;> simp [SzA.hLam]

private lemma SzA_hLam_one_zero (θ : K ≃+* K) (c : K) :
    SzA.hLam θ c (⟨1, 0⟩ : SzA K θ) = ⟨c, 0⟩ := by
  ext <;> simp [SzA.hLam]

private lemma SzA_hLam_zero_zero (θ : K ≃+* K) (c x : K) :
    SzA.hLam θ c (⟨x, 0⟩ : SzA K θ) = ⟨c * x, 0⟩ := by
  ext <;> simp [SzA.hLam]

private lemma SzA_zero_one_mul (θ : K ≃+* K) (c : K) :
    (⟨0, 1⟩ : SzA K θ) * ⟨0, c⟩ = ⟨0, 1 + c⟩ := by
  ext <;> simp [SzA.mul_a, SzA.mul_b]

private lemma SzA_one_one_sq (θ : K ≃+* K) :
    (⟨1, 1⟩ : SzA K θ) ^ 2 = (⟨0, 1⟩ : SzA K θ) := by
  rw [pow_two]
  simpa using SzA.sq_eq θ (⟨1, 1⟩ : SzA K θ)

private lemma SzA_target_mul (θ : K ≃+* K) (nu xi : K) :
    (⟨nu⁻¹ ^ 2 * xi⁻¹, 0⟩ : SzA K θ) * ⟨nu⁻¹, nu⁻¹ * θ nu⁻¹⟩
      = ⟨nu⁻¹ ^ 2 * xi⁻¹ + nu⁻¹, θ nu⁻¹ * (nu⁻¹ ^ 2 * xi⁻¹ + nu⁻¹)⟩ := by
  ext <;> simp only [SzA.mul_a, SzA.mul_b, zero_add] <;> ring

end Coords

/-- **HB III XI 11.13 (b), in the normalisation `e g = ⟨1,1⟩`:** the value that HB 11.10's
functional equation forces at the generic representatives.  With `X_ν = g⁻¹·(d g d⁻¹) =
e.symm ⟨1+ν, θν·(1+ν)⟩` (`d ∈ D` realising `h_ν`) and `ξ` any unit with
`ξ·θξ = 1 + ν⁻¹·θ(ν⁻¹)` (equivalently `φ_ξ(j) = j·φ_{ν⁻¹}(j)`, `j = g²`), one has
`f (X_ν) = φ_{ν⁻²ξ⁻¹}(g⁻¹)·φ_{ν⁻¹}(g) = ⟨ν⁻²ξ⁻¹+ν⁻¹, θ(ν⁻¹)·(ν⁻²ξ⁻¹+ν⁻¹)⟩`. -/
theorem frel_generic_value_eps {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m}
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {g : Q} (hg : e g = ⟨1, 1⟩)
    (hstruct : t * (((g ^ 2 : Q)) : G) * t = (g : G) * t * (((g⁻¹ : Q)) : G))
    (nu : (GaloisField 2 m)ˣ) (hnu : (nu : GaloisField 2 m) ≠ 1)
    (xi : (GaloisField 2 m)ˣ)
    (hxi : (xi : GaloisField 2 m) * θ (xi : GaloisField 2 m)
      = 1 + ((nu : GaloisField 2 m))⁻¹ * θ (((nu : GaloisField 2 m))⁻¹)) :
    Work.RankOneUniqueness.FRel H t
      (((e.symm ((⟨1 + (nu : GaloisField 2 m),
          θ (nu : GaloisField 2 m) * (1 + (nu : GaloisField 2 m))⟩ :
          Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ)) : Q)) : G)
      (((e.symm ((⟨((nu : GaloisField 2 m))⁻¹ ^ 2 * ((xi : GaloisField 2 m))⁻¹
            + ((nu : GaloisField 2 m))⁻¹,
          θ (((nu : GaloisField 2 m))⁻¹)
            * (((nu : GaloisField 2 m))⁻¹ ^ 2 * ((xi : GaloisField 2 m))⁻¹
                + ((nu : GaloisField 2 m))⁻¹)⟩ :
          Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ)) : Q)) : G) := by
  classical
  have ht2 : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hsplit
  -- the root group is nontrivial
  have hQne : Q ≠ ⊥ := by
    intro hbot
    have hmem : ((e.symm (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) : Q) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hbot]; exact (e.symm (⟨1, 0⟩ : SzA (GaloisField 2 m) θ)).2
    have h1 : ((e.symm (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) : Q) : G) = 1 :=
      Subgroup.mem_bot.mp hmem
    have h2 : (e.symm (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) : Q) = 1 := by
      apply Subtype.ext
      simpa using h1
    have h3 : (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) = 1 := by
      have := congrArg (fun q : Q => e q) h2
      simpa using this
    exact (one_ne_zero : (1 : GaloisField 2 m) ≠ 0) (by simpa using congrArg SzA.a h3)
  -- elementary coordinates of `g`
  have hge : e.symm (⟨1, 1⟩ : SzA (GaloisField 2 m) θ) = g := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply, hg]
  have hg2e : e (g ^ 2) = (⟨0, 1⟩ : SzA (GaloisField 2 m) θ) := by
    rw [map_pow, hg, SzA_one_one_sq]
  have hg2ne : g ^ 2 ≠ 1 := by
    intro h
    have : e (g ^ 2) = 1 := by rw [h, map_one]
    rw [hg2e] at this
    exact (one_ne_zero : (1 : GaloisField 2 m) ≠ 0) (by simpa using congrArg SzA.b this)
  have hge2 : e.symm (⟨0, 1⟩ : SzA (GaloisField 2 m) θ) = g ^ 2 := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply, hg2e]
  have hginv_e : e (g⁻¹) = (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) := by
    rw [map_inv, hg, SzA_inv_one_one]
  have hginv : (g⁻¹ : Q) = e.symm (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply, hginv_e]
  -- HB 11.13 (a)
  obtain ⟨hf1, hf2, hf3⟩ := frel_structure_values hsplit hg2ne hstruct
  -- torus elements realising `h_ν` and `h_ξ`
  obtain ⟨d, hdD, hdact⟩ := exists_torus_action hsplit hzass htorus nu
  obtain ⟨de, hdeD, hdeact⟩ := exists_torus_action hsplit hzass htorus xi
  have hdH : d ∈ H := hdD.1
  have hdt : t * d * t = d⁻¹ := by
    have h := twoPoint_inverted hsplit hzass hQne h2 d hdD
    rwa [inv_eq_of_mul_eq_one_right ht2] at h
  -- `d` realises `h_ν` on all of `Q`
  have hconj : ∀ w : SzA (GaloisField 2 m) θ,
      d * (((e.symm w : Q)) : G) * d⁻¹
        = (((e.symm (SzA.hLam θ (nu : GaloisField 2 m) w) : Q)) : G) := by
    intro w
    have h := hdact (e.symm w)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hconj_inv : ∀ w : SzA (GaloisField 2 m) θ,
      d⁻¹ * (((e.symm w : Q)) : G) * d
        = (((e.symm (SzA.hLam θ ((nu : GaloisField 2 m))⁻¹ w) : Q)) : G) := by
    intro w
    have hcomp : SzA.hLam θ (nu : GaloisField 2 m)
        (SzA.hLam θ ((nu : GaloisField 2 m))⁻¹ w) = w := by
      rw [← SzA.hLam_mul]
      have h1 : (nu : GaloisField 2 m) * (nu : GaloisField 2 m)⁻¹ = 1 := by simp
      rw [h1, SzA.hLam_one]
    have h := hconj (SzA.hLam θ ((nu : GaloisField 2 m))⁻¹ w)
    rw [hcomp] at h
    rw [← h]
    group
  -- the structure equation read as `t g t = g² t g`
  have hgt : t * (g : G) * t = (((g ^ 2 : Q)) : G) * t * (g : G) := by
    have h := congrArg (fun z => t * z) hstruct
    rw [show t * (t * (((g ^ 2 : Q)) : G) * t) = (((g ^ 2 : Q)) : G) * t by
          rw [show t * (t * (((g ^ 2 : Q)) : G) * t)
              = (t * t) * (((g ^ 2 : Q)) : G) * t by group, ht2, one_mul]] at h
    rw [show t * ((g : G) * t * (((g⁻¹ : Q)) : G))
        = t * (g : G) * t * (((g⁻¹ : Q)) : G) by group] at h
    have h2 : (((g ^ 2 : Q)) : G) * t * (g : G) = t * (g : G) * t := by
      rw [h]
      rw [show t * (g : G) * t * (((g⁻¹ : Q)) : G) * (g : G)
          = t * (g : G) * t * ((((g⁻¹ : Q)) : G) * (g : G)) by group]
      rw [show ((((g⁻¹ : Q)) : G) * (g : G)) = 1 by
            rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]]
      rw [mul_one]
    exact h2.symm
  -- explicit coordinates of the relevant conjugates
  have hdg : d * (g : G) * d⁻¹
      = (((e.symm (⟨(nu : GaloisField 2 m), (nu : GaloisField 2 m) * θ (nu : GaloisField 2 m)⟩
          : SzA (GaloisField 2 m) θ) : Q)) : G) := by
    have h := hconj (⟨1, 1⟩ : SzA (GaloisField 2 m) θ)
    rw [hge, SzA_hLam_one_one] at h
    exact h
  have hD1 : d⁻¹ * (g : G) * d
      = (((e.symm (⟨(nu : GaloisField 2 m)⁻¹,
          (nu : GaloisField 2 m)⁻¹ * θ ((nu : GaloisField 2 m)⁻¹)⟩
          : SzA (GaloisField 2 m) θ) : Q)) : G) := by
    have h := hconj_inv (⟨1, 1⟩ : SzA (GaloisField 2 m) θ)
    rw [hge, SzA_hLam_one_one] at h
    exact h
  -- the target element `X_ν = g⁻¹ · (d g d⁻¹)`
  have hA : ((g⁻¹ : Q) : G) * (d * (g : G) * d⁻¹)
      = (((e.symm (⟨1 + (nu : GaloisField 2 m),
          θ (nu : GaloisField 2 m) * (1 + (nu : GaloisField 2 m))⟩
          : SzA (GaloisField 2 m) θ) : Q)) : G) := by
    rw [hdg, hginv, ← Subgroup.coe_mul, ← map_mul]
    rw [SzA_one_zero_mul θ (nu : GaloisField 2 m)]
  -- `X_ν ≠ 1`
  have hXne : ((g⁻¹ : Q) : G) * (d * (g : G) * d⁻¹) ≠ 1 := by
    rw [hA]
    intro h
    have h2 : (e.symm (⟨1 + (nu : GaloisField 2 m),
        θ (nu : GaloisField 2 m) * (1 + (nu : GaloisField 2 m))⟩
        : SzA (GaloisField 2 m) θ) : Q) = 1 := by
      apply Subtype.ext
      simpa using h
    have h3 : (⟨1 + (nu : GaloisField 2 m),
        θ (nu : GaloisField 2 m) * (1 + (nu : GaloisField 2 m))⟩
        : SzA (GaloisField 2 m) θ) = 1 := by
      have := congrArg (fun q : Q => e q) h2
      simpa using this
    have h4 : (1 : GaloisField 2 m) + (nu : GaloisField 2 m) = 0 := by
      simpa using congrArg SzA.a h3
    have h5 : (nu : GaloisField 2 m) = 1 := by
      have : (1 : GaloisField 2 m) + (nu : GaloisField 2 m) = 1 + 1 := by
        rw [h4, CharTwo.add_self_eq_zero]
      exact add_left_cancel this
    exact hnu h5
  -- `d⁻¹ t d = (d⁻¹ d⁻¹) t`
  have hdtd : d⁻¹ * t * d = (d⁻¹ * d⁻¹) * t := by
    have h1 : d⁻¹ * t * d * t = d⁻¹ * d⁻¹ := by
      rw [show d⁻¹ * t * d * t = d⁻¹ * (t * d * t) by group, hdt]
    calc d⁻¹ * t * d = (d⁻¹ * t * d) * (t * t) := by rw [ht2, mul_one]
      _ = (d⁻¹ * t * d * t) * t := by group
      _ = (d⁻¹ * d⁻¹) * t := by rw [h1]
  -- conjugation by `t`, using `t * d * t = d⁻¹`
  have hcj : ∀ z : G, t * z * t = (MulAut.conj t) z := fun z => by
    rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_right ht2]
  have hswap : t * (d * (g : G) * d⁻¹) * t = d⁻¹ * (t * (g : G) * t) * d := by
    have hcd : (MulAut.conj t) d = d⁻¹ := by rw [← hcj d, hdt]
    have hcdi : (MulAut.conj t) (d⁻¹) = d := by rw [map_inv, hcd, inv_inv]
    rw [hcj (d * (g : G) * d⁻¹), map_mul, map_mul, hcd, hcdi, ← hcj (g : G)]
  -- the decomposition of `t x₂ t` for `x₂ = d g d⁻¹`
  have hdec : t * (d * (g : G) * d⁻¹) * t
      = (d⁻¹ * (((g ^ 2 : Q)) : G) * d) * (d⁻¹ * d⁻¹)
          * (t * (d⁻¹ * (g : G) * d)) := by
    rw [hswap, hgt]
    rw [show d⁻¹ * ((((g ^ 2 : Q)) : G) * t * (g : G)) * d
        = (d⁻¹ * (((g ^ 2 : Q)) : G) * d) * (d⁻¹ * t * d)
            * (d⁻¹ * (g : G) * d) by group]
    rw [hdtd]
    group
  have hb2mem : d⁻¹ * (((g ^ 2 : Q)) : G) * d ∈ Q := by
    have h := Subgroup.le_normalizer_iff.mp hsplit.normal d⁻¹ (H.inv_mem hdH)
      (((g ^ 2 : Q)) : G) (g ^ 2).2
    simpa using h
  have hg2mem : d⁻¹ * d⁻¹ ∈ twoPoint H t :=
    (twoPoint H t).mul_mem ((twoPoint H t).inv_mem hdD) ((twoPoint H t).inv_mem hdD)
  have hconj_gg : Work.RankOneUniqueness.FRel H t (d * (g : G) * d⁻¹) (d⁻¹ * (g : G) * d) :=
    frel_conj hdH ht2 hdt hf2
  -- `π = g² · (d⁻¹ g d)²` has the coordinates of `h_ξ (g²)`
  have hdinv_g2 : d⁻¹ * (((e.symm (⟨0, 1⟩ : SzA (GaloisField 2 m) θ) : Q)) : G) * d
      = (((e.symm (⟨0, (nu : GaloisField 2 m)⁻¹ * θ ((nu : GaloisField 2 m)⁻¹)⟩
          : SzA (GaloisField 2 m) θ) : Q)) : G) := by
    rw [hconj_inv (⟨0, 1⟩ : SzA (GaloisField 2 m) θ)]
    congr 1
    rw [SzA_hLam_zero_one]
  have hg2co : (((g ^ 2 : Q)) : G) = (((e.symm (⟨0, 1⟩ : SzA (GaloisField 2 m) θ) : Q)) : G) := by
    rw [hge2]
  have hpi_eq : (((g ^ 2 : Q)) : G) * (d⁻¹ * (((g ^ 2 : Q)) : G) * d)
      = (((e.symm (⟨0, (xi : GaloisField 2 m) * θ (xi : GaloisField 2 m)⟩
          : SzA (GaloisField 2 m) θ) : Q)) : G) := by
    rw [hg2co, hdinv_g2, ← Subgroup.coe_mul, ← map_mul]
    rw [show (⟨0, 1⟩ : SzA (GaloisField 2 m) θ)
          * ⟨0, (nu : GaloisField 2 m)⁻¹ * θ ((nu : GaloisField 2 m)⁻¹)⟩
        = ⟨0, (xi : GaloisField 2 m) * θ (xi : GaloisField 2 m)⟩ by
          rw [SzA_zero_one_mul, ← hxi]]
  have harg1 : (((e.symm (SzA.hLam θ (xi : GaloisField 2 m) (e (g ^ 2))) : Q)) : G)
      = (((g ^ 2 : Q)) : G) * (d⁻¹ * (((g ^ 2 : Q)) : G) * d) := by
    rw [hpi_eq]
    congr 1
    rw [hg2e, SzA_hLam_zero_one]
  have harg2 : (((e.symm (SzA.hLam θ (↑(xi⁻¹) : GaloisField 2 m) (e (g⁻¹))) : Q)) : G)
      = (((e.symm (⟨(xi : GaloisField 2 m)⁻¹, 0⟩ : SzA (GaloisField 2 m) θ) : Q)) : G) := by
    have hval : (↑(xi⁻¹) : GaloisField 2 m) = ((xi : GaloisField 2 m))⁻¹ :=
      Units.val_inv_eq_inv_val xi
    rw [hval]
    congr 1
    rw [hginv_e, SzA_hLam_one_zero]
  have hz_raw := frel_torus_inv hsplit hzass hQne h2 θ e hdeD xi hdeact hf1
  rw [harg1, harg2] at hz_raw
  -- assemble with the product relation
  have hmain := frel_product hsplit hzass h2 hXne hf3 hconj_gg hb2mem hg2mem hdec
    (pi := (((g ^ 2 : Q)) : G) * (d⁻¹ * (((g ^ 2 : Q)) : G) * d))
    (z := (((e.symm (⟨(xi : GaloisField 2 m)⁻¹, 0⟩ : SzA (GaloisField 2 m) θ) : Q)) : G))
    rfl hz_raw
  -- the two arguments of `hmain` are `X_ν` and the stated value
  have hstep1 : d⁻¹ * (((e.symm (⟨(xi : GaloisField 2 m)⁻¹, 0⟩
        : SzA (GaloisField 2 m) θ) : Q)) : G) * d
      = (((e.symm (⟨(nu : GaloisField 2 m)⁻¹ * (xi : GaloisField 2 m)⁻¹, 0⟩
          : SzA (GaloisField 2 m) θ) : Q)) : G) := by
    rw [hconj_inv (⟨(xi : GaloisField 2 m)⁻¹, 0⟩ : SzA (GaloisField 2 m) θ)]
    congr 1
    rw [SzA_hLam_zero_zero]
  have hstep : d⁻¹ * (d⁻¹ * (((e.symm (⟨(xi : GaloisField 2 m)⁻¹, 0⟩
        : SzA (GaloisField 2 m) θ) : Q)) : G) * d) * d
      = (((e.symm (⟨((nu : GaloisField 2 m))⁻¹ ^ 2 * ((xi : GaloisField 2 m))⁻¹, 0⟩
          : SzA (GaloisField 2 m) θ) : Q)) : G) := by
    rw [hstep1, hconj_inv (⟨(nu : GaloisField 2 m)⁻¹ * (xi : GaloisField 2 m)⁻¹, 0⟩
      : SzA (GaloisField 2 m) θ)]
    rw [show SzA.hLam θ ((nu : GaloisField 2 m))⁻¹
          (⟨(nu : GaloisField 2 m)⁻¹ * (xi : GaloisField 2 m)⁻¹, 0⟩
            : SzA (GaloisField 2 m) θ)
        = ⟨((nu : GaloisField 2 m))⁻¹ ^ 2 * ((xi : GaloisField 2 m))⁻¹, 0⟩ by
          rw [SzA_hLam_zero_zero]; congr 1; ring]
  have hB : (d⁻¹ * d⁻¹) * (((e.symm (⟨(xi : GaloisField 2 m)⁻¹, 0⟩
          : SzA (GaloisField 2 m) θ) : Q)) : G) * (d⁻¹ * d⁻¹)⁻¹ * (d⁻¹ * (g : G) * d)
      = (((e.symm (⟨((nu : GaloisField 2 m))⁻¹ ^ 2 * ((xi : GaloisField 2 m))⁻¹
            + ((nu : GaloisField 2 m))⁻¹,
          θ (((nu : GaloisField 2 m))⁻¹)
            * (((nu : GaloisField 2 m))⁻¹ ^ 2 * ((xi : GaloisField 2 m))⁻¹
                + ((nu : GaloisField 2 m))⁻¹)⟩
          : SzA (GaloisField 2 m) θ) : Q)) : G) := by
    rw [show (d⁻¹ * d⁻¹) * (((e.symm (⟨(xi : GaloisField 2 m)⁻¹, 0⟩
              : SzA (GaloisField 2 m) θ) : Q)) : G) * (d⁻¹ * d⁻¹)⁻¹ * (d⁻¹ * (g : G) * d)
          = (d⁻¹ * (d⁻¹ * (((e.symm (⟨(xi : GaloisField 2 m)⁻¹, 0⟩
              : SzA (GaloisField 2 m) θ) : Q)) : G) * d) * d) * (d⁻¹ * (g : G) * d) by group]
    rw [hstep, hD1, ← Subgroup.coe_mul, ← map_mul]
    rw [SzA_target_mul θ (nu : GaloisField 2 m) (xi : GaloisField 2 m)]
  rw [hA, hB] at hmain
  exact hmain

end Work.ZassenhausSuzuki
