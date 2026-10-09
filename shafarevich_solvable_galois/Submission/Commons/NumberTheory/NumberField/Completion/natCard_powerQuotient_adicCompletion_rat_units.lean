import Mathlib
import Submission.Commons.Analysis.Nonarchimedean.val_pow_sub_one_le_exp_neg
import Submission.Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion_log_val_eq
import Submission.Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow
import Submission.Commons.NumberTheory.NumberField.Completion.card_residueField_adicCompletionIntegers_eq_pow_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.exists_pow_mul_eq_int_adicCompletion_rat
import Submission.Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_residueClass
import Submission.Commons.NumberTheory.NumberField.mem_of_primesEquiv_eq
import Submission.Commons.NumberTheory.NumberField.Completion.mem_ker_units_residue_adicCompletion_iff
import Submission.Commons.NumberTheory.NumberField.Completion.surjective_units_residue_adicCompletion
import Submission.Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
import Submission.Commons.GroupTheory.SpecificGroups.Cyclic.card_quotient_powMonoidHom
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_eq_mul_of_exists_open_subgroup_units_tate_trivial
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField
open scoped WithZero
open IsDedekindDomain.HeightOneSpectrum

namespace Commons.NumberTheory.NumberField.Completion

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-! ## A general group-theoretic cardinality computation

For a surjective homomorphism `φ : G →* H` of commutative groups with no nontrivial `n`-torsion
in `H`, the quotient of `G` by its `n`-th powers decomposes as the product of the quotient of `H`
by its `n`-th powers and the quotient of `ker φ` by its `n`-th powers. -/

theorem natCard_quot_powMonoidHom_eq_mul {G H : Type*} [CommGroup G] [CommGroup H]
    (φ : G →* H) (hφ : Function.Surjective φ) (n : ℕ) [NeZero n]
    (htor : ∀ h : H, h ^ n = 1 → h = 1) :
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
      Nat.card (H ⧸ (powMonoidHom n : H →* H).range) *
        Nat.card (φ.ker ⧸ (powMonoidHom n : φ.ker →* φ.ker).range) := by
  let R : Subgroup G := (powMonoidHom n : G →* G).range
  have hKR : R.subgroupOf φ.ker = (powMonoidHom n : φ.ker →* φ.ker).range := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hx
      simp only [powMonoidHom_apply] at hg
      have hpg : φ g ^ n = 1 := by
        have hx1 : φ (x : G) = 1 := x.2
        rw [← map_pow, hg, hx1]
      have hgK : φ g = 1 := htor (φ g) hpg
      exact MonoidHom.mem_range.mpr ⟨⟨g, hgK⟩, Subtype.ext hg⟩
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hx
      rw [← hk]
      exact MonoidHom.mem_range.mpr ⟨(k : G), by rfl⟩
  have hmap : (φ.ker ⊔ R).map φ = (powMonoidHom n : H →* H).range := by
    rw [Subgroup.map_sup]
    have hKmap : (φ.ker).map φ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
    have hRmap : R.map φ = (powMonoidHom n : H →* H).range := by
      show ((powMonoidHom n : G →* G).range).map φ = _
      rw [MonoidHom.map_range]
      ext y
      constructor
      · rintro ⟨g, hg⟩
        exact ⟨φ g, by rw [← hg]; simp only [MonoidHom.comp_apply, powMonoidHom_apply, map_pow]⟩
      · rintro ⟨h, hh⟩
        obtain ⟨g, rfl⟩ := hφ h
        exact ⟨g, by rw [MonoidHom.comp_apply, powMonoidHom_apply, map_pow, ← hh, powMonoidHom_apply]⟩
    rw [hKmap, hRmap, bot_sup_eq]
  have h1 : (φ.ker ⊔ R : Subgroup G).index = (powMonoidHom n : H →* H).range.index := by
    have hS := Subgroup.index_map_eq (φ.ker ⊔ R : Subgroup G) hφ
      (le_sup_left : φ.ker ≤ (φ.ker ⊔ R : Subgroup G))
    rw [hmap] at hS
    exact hS.symm
  have h2 : R.relIndex (φ.ker ⊔ R : Subgroup G)
      = Nat.card (φ.ker ⧸ (powMonoidHom n : φ.ker →* φ.ker).range) := by
    show Nat.card ((φ.ker ⊔ R : Subgroup G) ⧸ R.subgroupOf (φ.ker ⊔ R)) = _
    rw [← Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient φ.ker R).toEquiv]
    rw [hKR]
  calc Nat.card (G ⧸ R) = R.index := rfl
    _ = R.relIndex (φ.ker ⊔ R : Subgroup G) * (φ.ker ⊔ R : Subgroup G).index :=
        (Subgroup.relIndex_mul_index (le_sup_right : R ≤ (φ.ker ⊔ R : Subgroup G))).symm
    _ = R.relIndex (φ.ker ⊔ R : Subgroup G) * (powMonoidHom n : H →* H).range.index := by rw [h1]
    _ = Nat.card (φ.ker ⧸ (powMonoidHom n : φ.ker →* φ.ker).range) *
          (powMonoidHom n : H →* H).range.index := by rw [h2]
    _ = Nat.card (φ.ker ⧸ (powMonoidHom n : φ.ker →* φ.ker).range) *
          Nat.card (H ⧸ (powMonoidHom n : H →* H).range) := rfl
    _ = Nat.card (H ⧸ (powMonoidHom n : H →* H).range) *
          Nat.card (φ.ker ⧸ (powMonoidHom n : φ.ker →* φ.ker).range) := by ring


/-- The predicate "every element of `1 + 𝔪 ^ k` is a `p`-th power of an element of `1 + 𝔪`",
formulated for a valued field `F` with value group `ℤᵐ⁰`. -/
def PpowRat (F : Type*) [Field F] (vv : Valuation F Zstar0) (p : ℕ) (k : ℕ) : Prop :=
  ∀ u : F, vv (u - 1) ≤ WithZero.exp (-(k : ℤ)) →
    ∃ y : F, vv (y - 1) ≤ WithZero.exp (-1) ∧ y ^ p = u

theorem powQuotRat_exp_neg_lt_one {n : ℕ} (hn : 1 ≤ n) :
    (WithZero.exp (-(n:ℤ)) : Zstar0) < 1 := by
  have h : WithZero.exp (-(n:ℤ)) < WithZero.exp (0:ℤ) := by
    rw [WithZero.exp_lt_exp]; omega
  simpa using h

theorem powQuotRat_val_eq_one_of_val_sub_one_lt_one {F : Type*} [Field F]
    (vv : Valuation F Zstar0) {x : F} (h : vv (x - 1) < 1) : vv x = 1 := by
  have h' := Valuation.map_add_eq_of_lt_left vv (x := (1:F)) (y := x - 1) (by simpa using h)
  rwa [show (1:F) + (x-1) = x by ring, Valuation.map_one] at h'

theorem powQuotRat_val_natCast_le_exp_neg_one {F : Type*} [Field F] (vv : Valuation F Zstar0)
    {p n : ℕ} (hvalp : vv ((p : ℕ) : F) = WithZero.exp (-1 : ℤ)) (hdvd : p ∣ n) :
    vv ((n : ℕ) : F) ≤ WithZero.exp (-1 : ℤ) := by
  obtain ⟨m, rfl⟩ := hdvd
  rw [Nat.cast_mul, Valuation.map_mul, hvalp]
  calc WithZero.exp (-1:ℤ) * vv ((m:ℕ):F)
      ≤ WithZero.exp (-1:ℤ) * 1 :=
        mul_le_mul' (le_refl _) (Commons.Analysis.Nonarchimedean.val_natCast_le_one vv m)
    _ = WithZero.exp (-1:ℤ) := mul_one _

theorem powQuotRat_pow_le_exp {F : Type*} [Field F] (vv : Valuation F Zstar0) {x : F} {a : ℤ}
    (hx : vv x ≤ WithZero.exp a) (n : ℕ) :
    vv (x^n) ≤ WithZero.exp ((n:ℤ) * a) := by
  rw [Valuation.map_pow]
  calc vv x ^ n ≤ (WithZero.exp a)^n := pow_le_pow_left' hx n
    _ = WithZero.exp ((n:ℤ) * a) := by
        rw [← WithZero.exp_nsmul, nsmul_eq_mul]

theorem powQuotRat_mul_pow_le_exp {F : Type*} [Field F] (vv : Valuation F Zstar0)
    {x y : F} {a b : ℤ} (hx : vv x ≤ WithZero.exp a) (hy : vv y ≤ WithZero.exp b) (n : ℕ) :
    vv (x^n * y) ≤ WithZero.exp ((n:ℤ) * a + b) := by
  rw [Valuation.map_mul]
  calc vv (x^n) * vv y ≤ WithZero.exp ((n:ℤ)*a) * WithZero.exp b :=
        mul_le_mul' (powQuotRat_pow_le_exp vv hx n) hy
    _ = WithZero.exp ((n:ℤ)*a + b) := (WithZero.exp_add _ _).symm

/-- Base case of the bootstrap: `1 + 𝔪 ^ (M+1)` is contained in the `p`-th powers of
`1 + 𝔪`, where `M` is the depth of the `p`-adic logarithm. -/
theorem powQuotRat_base {F : Type*} [Field F] (vv : Valuation F Zstar0) (p M : ℕ)
    (hp : p.Prime) (hp0 : ((p:ℕ):F) ≠ 0)
    (hM : 1 ≤ M) (exp log : F → F)
    (hexp0 : exp 0 = 1)
    (hexpm1 : ∀ x : F, vv x ≤ WithZero.exp (-(M:ℤ)) → vv (exp x - 1) = vv x)
    (hexpadd : ∀ x y : F, vv x ≤ WithZero.exp (-(M:ℤ)) → vv y ≤ WithZero.exp (-(M:ℤ)) →
      exp (x + y) = exp x * exp y)
    (hlogval : ∀ y : F, vv (y - 1) ≤ WithZero.exp (-(M:ℤ)) → vv (log y) = vv (y-1))
    (hloginv : ∀ y : F, vv (y - 1) ≤ WithZero.exp (-(M:ℤ)) → exp (log y) = y)
    (hvalp : vv ((p : ℕ) : F) = WithZero.exp (-1 : ℤ)) :
    PpowRat F vv p (M + 1) := by
  intro u hu
  by_cases hu1 : u = 1
  · refine ⟨1, ?_, ?_⟩
    · rw [sub_self, map_zero]; exact bot_le
    · rw [hu1]; exact one_pow p
  have hle1 : WithZero.exp (-(M:ℤ)) ≤ (WithZero.exp (-1 : ℤ) : Zstar0) := by
    rw [WithZero.exp_le_exp]; omega
  have huM : vv (u - 1) ≤ WithZero.exp (-(M:ℤ)) := by
    refine le_trans hu ?_
    rw [WithZero.exp_le_exp]; push_cast; omega
  have hlt1 : vv (u - 1) < (1 : Zstar0) := by
    refine lt_of_le_of_lt huM ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hvalu : vv u = 1 := powQuotRat_val_eq_one_of_val_sub_one_lt_one vv (by simpa using hlt1)
  set z : F := log u / ((p:ℕ):F) with hzdef
  have hzval : vv z ≤ WithZero.exp (-(M:ℤ)) := by
    rw [hzdef, Valuation.map_div, hlogval u huM, hvalp, div_eq_mul_inv]
    have h1 : (WithZero.exp (-1 : ℤ))⁻¹ = (WithZero.exp (1 : ℤ) : Zstar0) := by
      rw [← WithZero.exp_neg]; norm_num
    rw [h1]
    calc vv (u - 1) * WithZero.exp (1 : ℤ)
        ≤ WithZero.exp (-((M+1:ℕ):ℤ)) * WithZero.exp (1 : ℤ) :=
          mul_le_mul' hu (le_refl _)
      _ = WithZero.exp (-(M:ℤ)) := by
          rw [← WithZero.exp_add]; congr 1; push_cast; ring
  have hdisk : ∀ m : ℕ, vv ((m:ℕ) • z) ≤ WithZero.exp (-(M:ℤ)) := by
    intro m
    rw [nsmul_eq_mul, Valuation.map_mul]
    calc vv ((m:ℕ):F) * vv z ≤ 1 * WithZero.exp (-(M:ℤ)) :=
          mul_le_mul' (Commons.Analysis.Nonarchimedean.val_natCast_le_one vv m) hzval
      _ = WithZero.exp (-(M:ℤ)) := one_mul _
  have hpow_exp : ∀ m : ℕ, exp ((m:ℕ) • z) = (exp z)^m := by
    intro m; induction m with
    | zero => rw [zero_nsmul, hexp0, pow_zero]
    | succ m ih =>
      rw [succ_nsmul, hexpadd _ _ (hdisk m) hzval, ih, pow_succ]
  have hzlog : (p:ℕ) • z = log u := by
    rw [hzdef, nsmul_eq_mul]
    field_simp
  refine ⟨exp z, ?_, ?_⟩
  · rw [hexpm1 z hzval]
    exact le_trans hzval hle1
  · rw [← hpow_exp p, hzlog, hloginv u huM]

/-- One bootstrap step: if `1 + 𝔪 ^ (k+1)` is contained in the `p`-th powers of `1 + 𝔪`,
then so is `1 + 𝔪 ^ k`.  The correction term in Newton's method is small enough because the
binomial coefficients `C(p,j)` for `2 ≤ j ≤ p-1` are divisible by `p`. -/
theorem powQuotRat_step {F : Type*} [Field F] (vv : Valuation F Zstar0) (p k : ℕ)
    (hp : p.Prime) (hodd : p ≠ 2) (hk : 2 ≤ k) (hp0 : ((p:ℕ):F) ≠ 0)
    (hvalp : vv ((p : ℕ) : F) = WithZero.exp (-1 : ℤ))
    (hP : PpowRat F vv p (k+1)) :
    PpowRat F vv p k := by
  intro u hu
  by_cases hu1 : u = 1
  · refine ⟨1, ?_, ?_⟩
    · rw [sub_self, map_zero]; exact bot_le
    · rw [hu1]; exact one_pow p
  set t : F := (u - 1) / ((p:ℕ):F) with htdef
  have htval : vv t ≤ WithZero.exp (-(k:ℤ) + 1) := by
    rw [htdef, Valuation.map_div, hvalp, div_eq_mul_inv]
    have h1 : (WithZero.exp (-1 : ℤ))⁻¹ = (WithZero.exp (1 : ℤ) : Zstar0) := by
      rw [← WithZero.exp_neg]; norm_num
    rw [h1]
    calc vv (u - 1) * WithZero.exp (1:ℤ)
        ≤ WithZero.exp (-(k:ℤ)) * WithZero.exp (1:ℤ) := mul_le_mul' hu (le_refl _)
      _ = WithZero.exp (-(k:ℤ) + 1) := by rw [← WithZero.exp_add]
  have htk : WithZero.exp (-(k:ℤ) + 1) ≤ (WithZero.exp (-1:ℤ) : Zstar0) := by
    rw [WithZero.exp_le_exp]; omega
  have htval1 : vv t ≤ WithZero.exp (-1 : ℤ) := le_trans htval htk
  have hpt : ((p:ℕ):F) * t = u - 1 := by
    rw [htdef]; field_simp
  set y0 : F := 1 + t with hy0def
  have hy0val : vv (y0 - 1) ≤ WithZero.exp (-1 : ℤ) := by
    rw [hy0def]
    have : (1:F) + t - 1 = t := by ring
    rw [this]; exact htval1
  have hy0one : vv y0 = 1 := by
    have hlt : vv (y0 - 1) < (1:Zstar0) := lt_of_le_of_lt hy0val (powQuotRat_exp_neg_lt_one le_rfl)
    exact powQuotRat_val_eq_one_of_val_sub_one_lt_one vv hlt
  have hident : (1 + t)^p - u
      = ∑ j ∈ Finset.range (p-1), t^(j+2) * ((p.choose (j+2) : ℕ) : F) := by
    have hbin := Commons.Analysis.Nonarchimedean.val_pow_sub_one_binomial_split t hp.one_le
    have hrw : (1 + t)^p - u = ((1+t)^p - 1) + (1 - u) := by ring
    rw [hrw, hbin, hpt]; ring
  have hE : vv ((1 + t)^p - u) ≤ WithZero.exp (-(k:ℤ) - 1) := by
    rw [hident]
    apply Valuation.map_sum_le
    intro j hj
    rw [Finset.mem_range] at hj
    have hjp : j + 2 ≤ p := by omega
    rcases lt_or_eq_of_le hjp with hlt | heq
    · have hdvd : p ∣ p.choose (j+2) := hp.dvd_choose_self (by omega) hlt
      have hC : vv (((p.choose (j+2) : ℕ)) : F) ≤ WithZero.exp (-1:ℤ) :=
        powQuotRat_val_natCast_le_exp_neg_one vv hvalp hdvd
      calc vv (t^(j+2) * ((p.choose (j+2) : ℕ) : F))
          ≤ WithZero.exp (((j+2:ℕ):ℤ) * (-(k:ℤ)+1) + (-1)) :=
            powQuotRat_mul_pow_le_exp vv htval hC (j+2)
        _ ≤ WithZero.exp (-(k:ℤ) - 1) := by
            rw [WithZero.exp_le_exp]
            have hj0 : (0:ℤ) ≤ (j:ℤ) := Int.natCast_nonneg j
            have hk2 : (2:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk
            push_cast
            nlinarith
    · have hC1 : ((p.choose (j+2) : ℕ) : F) = 1 := by rw [heq, Nat.choose_self]; norm_num
      rw [hC1, mul_one]
      calc vv (t^(j+2)) ≤ WithZero.exp (((j+2:ℕ):ℤ) * (-(k:ℤ)+1)) :=
            powQuotRat_pow_le_exp vv htval (j+2)
        _ ≤ WithZero.exp (-(k:ℤ) - 1) := by
            rw [WithZero.exp_le_exp]
            have hjp' : ((j+2 : ℕ) : ℤ) = (p:ℤ) := by rw [heq]
            have hp3 : (3:ℤ) ≤ (p:ℤ) := by
              have h2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
              exact_mod_cast h2
            have hk2 : (2:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk
            rw [hjp']
            nlinarith
  have huone : vv u = 1 := by
    refine powQuotRat_val_eq_one_of_val_sub_one_lt_one vv ?_
    refine lt_of_le_of_lt hu ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hune : u ≠ 0 := (Valuation.ne_zero_iff vv).mp (by rw [huone]; exact one_ne_zero)
  set w : F := (1+t)^p / u with hwdef
  have hwval : vv (w - 1) ≤ WithZero.exp (-((k+1:ℕ):ℤ)) := by
    have hw : w - 1 = ((1+t)^p - u) / u := by
      rw [hwdef]; field_simp
    rw [hw, Valuation.map_div, huone, div_one]
    refine le_trans hE (le_of_eq ?_)
    congr 1; push_cast; ring
  obtain ⟨w₀, hw0val, hw0pow⟩ := hP w hwval
  have hw0one : vv w₀ = 1 := by
    have hlt : vv (w₀ - 1) < (1:Zstar0) := lt_of_le_of_lt hw0val (powQuotRat_exp_neg_lt_one le_rfl)
    exact powQuotRat_val_eq_one_of_val_sub_one_lt_one vv hlt
  have hw0ne : w₀ ≠ 0 := (Valuation.ne_zero_iff vv).mp (by rw [hw0one]; exact one_ne_zero)
  refine ⟨y0 / w₀, ?_, ?_⟩
  · have hyw : y0 / w₀ - 1 = (y0 - w₀)/w₀ := by field_simp
    rw [hyw, Valuation.map_div, hw0one, div_one]
    have heq2 : y0 - w₀ = (y0 - 1) - (w₀ - 1) := by ring
    rw [heq2]
    refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
    · exact hy0val
    · exact hw0val
  · have h1tne : (1 + t) ≠ 0 := by
      intro h
      have hh := hy0one
      rw [hy0def, h] at hh
      simp at hh
    rw [div_pow, hy0def, hw0pow, hwdef]
    field_simp

/-- **The key `p`-adic root statement.**  If `p` is an odd prime which is a uniformizer of the
valued field `F` (i.e. `vv p = exp (-1)`), then every element of `1 + 𝔪 ^ 2` is a `p`-th power of
an element of `1 + 𝔪`. -/
theorem powQuotRat_crux (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (hvalp : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0) ((p : ℚ) : v.adicCompletion ℚ)
      = WithZero.exp (-1 : ℤ)) :
    PpowRat (v.adicCompletion ℚ) (Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)) p 2 := by
  obtain ⟨M, hM1, exp, log, hexpsum, hexpm1, hexp0, hexpadd, hlog, hlogexp⟩ :=
    Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion_log_val_eq v
  have hvalp' : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0) ((p:ℕ) : v.adicCompletion ℚ) = WithZero.exp (-1:ℤ) := by
    rw [show ((p:ℕ) : v.adicCompletion ℚ) = ((p:ℚ) : v.adicCompletion ℚ) by push_cast; rfl]
    exact hvalp
  have hp0 : ((p:ℕ) : v.adicCompletion ℚ) ≠ 0 :=
    (Valuation.ne_zero_iff _).mp (by rw [hvalp']; exact WithZero.exp_ne_zero)
  have hbase : PpowRat (v.adicCompletion ℚ) (Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)) p (M+1) :=
    powQuotRat_base _ p M hp hp0 hM1 exp log hexp0 hexpm1 hexpadd
      (fun y hy => (hlog y hy).2.1) (fun y hy => (hlog y hy).2.2) hvalp'
  exact (Nat.decreasingInduction (n := M+1)
    (motive := fun m _ => 2 ≤ m → PpowRat (v.adicCompletion ℚ)
      (Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)) p m)
    (fun k hk hprev hk2 =>
      powQuotRat_step _ p k hp hodd hk2 hp0 hvalp' (hprev (by omega)))
    (fun _ => hbase)
    (m := 2) (by omega)) (le_refl 2)


/-! ## The map `1 + 𝔪 → κ` recording the "first digit" of a principal unit -/

abbrev piQ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    v.adicCompletionIntegers ℚ :=
  Commons.RingTheory.Henselian.uniformizer (R := NumberField.RingOfIntegers ℚ) (K := ℚ) v

theorem piQ_ne_zero (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    piQ v ≠ 0 :=
  (Commons.RingTheory.Henselian.uniformizer_irreducible
    (R := NumberField.RingOfIntegers ℚ) (K := ℚ) v).ne_zero

theorem maxIdeal_eq_span_piQ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) = Ideal.span {piQ v} :=
  Commons.RingTheory.Henselian.maximalIdeal_eq_span_uniformizer
    (R := NumberField.RingOfIntegers ℚ) (K := ℚ) v

theorem residue_piQ_eq_zero (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    IsLocalRing.residue (v.adicCompletionIntegers ℚ) (piQ v) = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, maxIdeal_eq_span_piQ]
  exact Ideal.mem_span_singleton.mpr (dvd_refl _)

abbrev KQ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    Subgroup (v.adicCompletionIntegers ℚ)ˣ :=
  (Units.map ((IsLocalRing.residue (v.adicCompletionIntegers ℚ)).toMonoidHom)).ker

theorem thetaCoeff_exists (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (u : KQ v) :
    ∃ c : v.adicCompletionIntegers ℚ,
      ((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1 = piQ v * c := by
  have hmem : ((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
      ∈ Ideal.span {piQ v} := by
    rw [← maxIdeal_eq_span_piQ v]
    exact (Commons.NumberTheory.NumberField.Completion.mem_ker_units_residue_iff
      (u : (v.adicCompletionIntegers ℚ)ˣ)).mp u.2
  exact dvd_def.mp (Ideal.mem_span_singleton.mp hmem)

def thetaCoeff (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (u : KQ v) :
    v.adicCompletionIntegers ℚ := Classical.choose (thetaCoeff_exists v u)

theorem thetaCoeff_spec (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (u : KQ v) :
    ((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
      = piQ v * thetaCoeff v u :=
  Classical.choose_spec (thetaCoeff_exists v u)

theorem thetaCoeff_unique (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {u : KQ v} {c : v.adicCompletionIntegers ℚ}
    (h : ((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1 = piQ v * c) :
    c = thetaCoeff v u := by
  have h1 := thetaCoeff_spec v u
  have h2 : piQ v * c = piQ v * thetaCoeff v u := by rw [← h, h1]
  exact mul_left_cancel₀ (piQ_ne_zero v) h2

def theta (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (u : KQ v) :
    IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ) :=
  IsLocalRing.residue _ (thetaCoeff v u)

theorem theta_mul (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (u w : KQ v) : theta v (u * w) = theta v u + theta v w := by
  set c := thetaCoeff v u with hc
  set d := thetaCoeff v w with hd
  have hu : ((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ)
      = 1 + piQ v * c := by rw [hc, ← thetaCoeff_spec v u]; ring
  have hw : ((w : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ)
      = 1 + piQ v * d := by rw [hd, ← thetaCoeff_spec v w]; ring
  have hcd : (((u * w : KQ v) : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
      = piQ v * (c + d + piQ v * c * d) := by
    rw [show (((u * w : KQ v) : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ)
        = ((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ)
          * ((w : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) by simp,
      hu, hw]
    ring
  have hkey : thetaCoeff v (u * w) = c + d + piQ v * c * d := (thetaCoeff_unique v hcd).symm
  simp only [theta, hkey, ← hc, ← hd, map_add, map_mul, residue_piQ_eq_zero]
  ring

def thetaHom (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    KQ v →* Multiplicative (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) where
  toFun u := Multiplicative.ofAdd (theta v u)
  map_one' := by
    have h0 : thetaCoeff v 1 = 0 := by
      have hspec : (((1 : KQ v) : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
          = piQ v * 0 := by simp
      exact (thetaCoeff_unique v hspec).symm
    simp only [theta, h0, map_zero, ofAdd_zero]
  map_mul' u w := by rw [theta_mul]; rfl

theorem thetaHom_apply (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (u : KQ v) : thetaHom v u = Multiplicative.ofAdd (theta v u) := rfl

theorem theta_surjective (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    Function.Surjective (theta v) := by
  intro b
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := v.adicCompletionIntegers ℚ) b
  have hxunit : IsUnit (1 + piQ v * a : v.adicCompletionIntegers ℚ) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_add, map_one, map_mul,
      residue_piQ_eq_zero, zero_mul, add_zero]
    exact one_ne_zero
  have hmem : (((hxunit.unit : (v.adicCompletionIntegers ℚ)ˣ)) : v.adicCompletionIntegers ℚ) - 1
      ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) := by
    rw [IsUnit.unit_spec, maxIdeal_eq_span_piQ]
    have h1 : (1 + piQ v * a : v.adicCompletionIntegers ℚ) - 1 = piQ v * a := by ring
    rw [h1]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
  have hker : hxunit.unit ∈ KQ v :=
    (Commons.NumberTheory.NumberField.Completion.mem_ker_units_residue_iff hxunit.unit).mpr hmem
  refine ⟨⟨hxunit.unit, hker⟩, ?_⟩
  have hspec : (((⟨hxunit.unit, hker⟩ : KQ v) : (v.adicCompletionIntegers ℚ)ˣ)
      : v.adicCompletionIntegers ℚ) - 1 = piQ v * a := by
    rw [IsUnit.unit_spec]
    ring
  have hcoe : thetaCoeff v ⟨hxunit.unit, hker⟩ = a := (thetaCoeff_unique v hspec).symm
  simp only [theta]
  rw [hcoe, ha]

theorem thetaHom_surjective (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    Function.Surjective (thetaHom v) := by
  intro b
  obtain ⟨u, hu⟩ := theta_surjective v (Multiplicative.toAdd b)
  exact ⟨u, by rw [thetaHom_apply, hu, ofAdd_toAdd]⟩

theorem theta_eq_zero_iff (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (u : KQ v) :
    theta v u = 0 ↔ ((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
      ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) ^ 2 := by
  simp only [theta]
  rw [IsLocalRing.residue_eq_zero_iff, thetaCoeff_spec v u]
  rw [maxIdeal_eq_span_piQ, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    Ideal.mem_span_singleton, dvd_def, dvd_def]
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d, by rw [hd]; ring⟩
  · rintro ⟨d, hd⟩
    exact ⟨d, mul_left_cancel₀ (piQ_ne_zero v) (by rw [hd]; ring)⟩

/-! ## The `p`-th powers of the principal units -/

theorem KQ_pow_range_le_ker (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (p : ℕ) (hp : p.Prime)
    (hvalpN : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((p:ℕ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ)) :
    (powMonoidHom p : KQ v →* KQ v).range ≤ (thetaHom v).ker := by
  rintro u ⟨w, rfl⟩
  rw [MonoidHom.mem_ker, thetaHom_apply, ofAdd_eq_one, theta_eq_zero_iff]
  have hwmem : ((w : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
      ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) :=
    (Commons.NumberTheory.NumberField.Completion.mem_ker_units_residue_iff
      (w : (v.adicCompletionIntegers ℚ)ˣ)).mp w.2
  have hxval : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((((w : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
        : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) ≤ WithZero.exp (-1 : ℤ) := by
    have := (val_le_exp_neg_iff_mem_maximalIdeal_pow v
      (((w : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1) 1)
    rw [pow_one] at this
    exact this.mpr hwmem
  have hstep := Commons.Analysis.Nonarchimedean.val_pow_sub_one_step
    (Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)) hp.one_le (le_of_eq hvalpN)
    (t := 1) le_rfl hxval
  have hmem2 : (((w : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) ^ p - 1)
      ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) ^ 2 := by
    rw [← (val_le_exp_neg_iff_mem_maximalIdeal_pow v
      (((w : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) ^ p - 1) 2)]
    have hcast : (((((w : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) ^ p - 1)
        : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)
        = (1 + ((((w : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
            : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)) ^ p - 1 := by
      push_cast; ring
    rw [hcast]
    exact hstep
  rw [powMonoidHom_apply]
  rwa [show ((↑(w ^ p : KQ v) : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ)
      = ((w : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) ^ p by simp]

theorem theta_ker_le_KQ_pow (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (hvalp : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((p:ℚ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ)) :
    (thetaHom v).ker ≤ (powMonoidHom p : KQ v →* KQ v).range := by
  intro u hu
  rw [MonoidHom.mem_range]
  have hu0 : ((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
      ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) ^ 2 := by
    rw [← theta_eq_zero_iff v u, ← ofAdd_eq_one, ← thetaHom_apply]
    exact MonoidHom.mem_ker.mp hu
  have hval2 : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
        : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) ≤ WithZero.exp (-2 : ℤ) := by
    have := (val_le_exp_neg_iff_mem_maximalIdeal_pow v
      (((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1) 2).mpr hu0
    simpa using this
  have hcrux := powQuotRat_crux v p hp hodd hvalp
    (((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)
    (by simpa using hval2)
  obtain ⟨y, hy1, hyp⟩ := hcrux
  have hylt : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0) (y - 1) < 1 :=
    lt_of_le_of_lt hy1 (powQuotRat_exp_neg_lt_one le_rfl)
  have hyval : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0) y = 1 :=
    powQuotRat_val_eq_one_of_val_sub_one_lt_one _ hylt
  have hymem : y ∈ v.adicCompletionIntegers ℚ :=
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      (NumberField.RingOfIntegers ℚ) ℚ v).mpr (le_of_eq hyval)
  have hyunit : IsUnit (⟨y, hymem⟩ : v.adicCompletionIntegers ℚ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hyval
  have hsubmem : ((hyunit.unit : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
      ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) := by
    rw [IsUnit.unit_spec]
    have hkey := (val_le_exp_neg_iff_mem_maximalIdeal_pow v (⟨y, hymem⟩ - 1) 1)
    rw [pow_one] at hkey
    exact hkey.mp (by
      rw [show (((⟨y, hymem⟩ : v.adicCompletionIntegers ℚ) - 1
        : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = y - 1 by push_cast; ring]
      exact hy1)
  refine ⟨⟨hyunit.unit, (Commons.NumberTheory.NumberField.Completion.mem_ker_units_residue_iff
    hyunit.unit).mpr hsubmem⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [powMonoidHom_apply, Subgroup.coe_pow, Subtype.coe_mk, Units.val_pow_eq_pow_val,
    IsUnit.unit_spec]
  exact Subtype.ext (by simpa using hyp)

theorem KQ_pow_range_eq_ker (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (hvalp : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((p:ℚ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ)) :
    (powMonoidHom p : KQ v →* KQ v).range = (thetaHom v).ker := by
  have hvalpN : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((p:ℕ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
    rw [show ((p:ℕ) : v.adicCompletion ℚ) = ((p:ℚ) : v.adicCompletion ℚ) by push_cast; rfl]
    exact hvalp
  exact le_antisymm (KQ_pow_range_le_ker v p hp hvalpN) (theta_ker_le_KQ_pow v p hp hodd hvalp)

/-! ## Cardinality of the relevant quotients -/

theorem gcd_prime_self_sub_one {p : ℕ} (hp : p.Prime) : Nat.gcd p (p - 1) = 1 := by
  have h1 : Nat.gcd p (p - 1) ∣ p := Nat.gcd_dvd_left p (p - 1)
  have h2 : Nat.gcd p (p - 1) ∣ p - 1 := Nat.gcd_dvd_right p (p - 1)
  have h3 : Nat.gcd p (p - 1) ∣ p - (p - 1) := Nat.dvd_sub h1 h2
  have h4 : p - (p - 1) = 1 := by have := hp.one_le; omega
  rw [h4] at h3
  exact Nat.dvd_one.mp h3

theorem ofAdd_pow_eq (m : ℤ) (p : ℕ) :
    (Multiplicative.ofAdd m) ^ p = Multiplicative.ofAdd ((p:ℤ) * m) := by
  rw [← ofAdd_nsmul, nsmul_eq_mul]

theorem ofAdd_zpow_eq (m k : ℤ) :
    (Multiplicative.ofAdd m) ^ k = Multiplicative.ofAdd (k * m) := by
  rw [← ofAdd_zsmul]
  congr 1

theorem natCard_multiplicative_int_quot_pow (p : ℕ) :
    Nat.card (Multiplicative ℤ ⧸ (powMonoidHom p : Multiplicative ℤ →* Multiplicative ℤ).range)
      = p := by
  have hrange : (powMonoidHom p : Multiplicative ℤ →* Multiplicative ℤ).range
      = Subgroup.zpowers (Multiplicative.ofAdd (p:ℤ)) := by
    ext x
    rw [MonoidHom.mem_range, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨m, rfl⟩
      rw [powMonoidHom_apply]
      refine ⟨Multiplicative.toAdd m, ?_⟩
      rw [ofAdd_zpow_eq]
      conv_rhs => rw [← ofAdd_toAdd m]
      rw [ofAdd_pow_eq]
      congr 1; ring
    · rintro ⟨k, rfl⟩
      refine ⟨Multiplicative.ofAdd k, ?_⟩
      rw [powMonoidHom_apply, ofAdd_pow_eq, ofAdd_zpow_eq]
      congr 1; ring
  rw [hrange, ← Subgroup.index_eq_card, Commons.GroupTheory.Subgroup.index_zpowers_ofAdd]
  exact Int.natAbs_natCast p

theorem natCard_residue_units_quot_pow
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (p : ℕ)
    (hp : p.Prime)
    (hres : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = p) :
    Nat.card ((IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))ˣ ⧸
      (powMonoidHom p).range) = 1 := by
  haveI hfin : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion ℚ v
  haveI : Fintype (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := Fintype.ofFinite _
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))ˣ :=
    Finite.of_injective (Units.val : (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))ˣ → IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) Units.val_injective
  haveI : Fintype (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))ˣ := Fintype.ofFinite _
  rw [Commons.GroupTheory.SpecificGroups.Cyclic.card_quotient_powMonoidHom
    (G := (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))ˣ) p,
    ← Nat.card_eq_fintype_card, Nat.card_units, hres]
  exact gcd_prime_self_sub_one hp

theorem natCard_KQ_quot_pow
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (p : ℕ)
    (hp : p.Prime) (hodd : p ≠ 2)
    (hvalp : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((p:ℚ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (hres : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = p) :
    Nat.card (KQ v ⧸ (powMonoidHom p : KQ v →* KQ v).range) = p := by
  rw [KQ_pow_range_eq_ker v p hp hodd hvalp]
  haveI hfin : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion ℚ v
  haveI : Fintype (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := Fintype.ofFinite _
  have h := QuotientGroup.quotientKerEquivOfSurjective (thetaHom v) (thetaHom_surjective v)
  rw [Nat.card_congr h.toEquiv, ← Nat.card_congr (Multiplicative.ofAdd (α := IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)))]
  exact hres

theorem natCard_adicCompletionIntegers_units_quot_pow
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (p : ℕ)
    (hp : p.Prime) (hodd : p ≠ 2)
    (hvalp : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((p:ℚ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (hres : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = p) :
    Nat.card ((v.adicCompletionIntegers ℚ)ˣ ⧸ (powMonoidHom p).range) = p := by
  haveI hfin : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion ℚ v
  haveI : Fintype (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := Fintype.ofFinite _
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))ˣ :=
    Finite.of_injective (Units.val : (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))ˣ → IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) Units.val_injective
  haveI : Fintype (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))ˣ := Fintype.ofFinite _
  have htor : ∀ h : (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))ˣ, h ^ p = 1 → h = 1 := by
    intro h hh
    have h1 : orderOf h ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hh
    have h2 : orderOf h ∣ p - 1 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      have hc : Fintype.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))ˣ = p - 1 := by
        rw [← Nat.card_eq_fintype_card, Nat.card_units, hres]
      rw [← hc]
      exact pow_card_eq_one
    have h3 : orderOf h ∣ Nat.gcd p (p - 1) := Nat.dvd_gcd h1 h2
    rw [gcd_prime_self_sub_one hp] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have htot := natCard_quot_powMonoidHom_eq_mul
    (Units.map ((IsLocalRing.residue (v.adicCompletionIntegers ℚ)).toMonoidHom))
    (Commons.NumberTheory.NumberField.Completion.surjective_units_residue_adicCompletion v)
    p htor
  rw [htot, natCard_residue_units_quot_pow v p hp hres,
    natCard_KQ_quot_pow v p hp hodd hvalp hres, one_mul]

theorem natCard_ker_unitsValLog_quot_pow
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (p : ℕ)
    (hp : p.Prime) (hodd : p ≠ 2)
    (hvalp : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((p:ℚ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (hres : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = p) :
    Nat.card ((unitsValLog (v.adicCompletion ℚ)).ker ⧸
      (powMonoidHom p : (unitsValLog (v.adicCompletion ℚ)).ker →*
        (unitsValLog (v.adicCompletion ℚ)).ker).range) = p := by
  have hA := natCard_adicCompletionIntegers_units_quot_pow v p hp hodd hvalp hres
  have hker : (unitsValLog (v.adicCompletion ℚ)).ker = (v.adicCompletionIntegers ℚ).unitGroup :=
    Commons.NumberTheory.NumberField.Completion.adicUnitsVal_eq_unitGroup ℚ v
  rw [hker]
  have he : ((powMonoidHom p : (v.adicCompletionIntegers ℚ).unitGroup →*
        (v.adicCompletionIntegers ℚ).unitGroup).range).map
        (ValuationSubring.unitGroupMulEquiv (v.adicCompletionIntegers ℚ))
      = (powMonoidHom p : (v.adicCompletionIntegers ℚ)ˣ →* (v.adicCompletionIntegers ℚ)ˣ).range := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨k, hk, hkx⟩ := hx
      rw [MonoidHom.mem_range] at hk
      obtain ⟨g, hg⟩ := hk
      have hgk : g ^ p = k := by simpa [powMonoidHom_apply] using hg
      rw [MonoidHom.mem_range]
      refine ⟨ValuationSubring.unitGroupMulEquiv _ g, ?_⟩
      rw [powMonoidHom_apply, ← map_pow, hgk]
      exact hkx
    · intro hx
      rw [MonoidHom.mem_range] at hx
      obtain ⟨k, hk⟩ := hx
      rw [Subgroup.mem_map]
      refine ⟨(ValuationSubring.unitGroupMulEquiv (v.adicCompletionIntegers ℚ)).symm (k ^ p), ?_, ?_⟩
      · rw [MonoidHom.mem_range]
        exact ⟨(ValuationSubring.unitGroupMulEquiv (v.adicCompletionIntegers ℚ)).symm k,
          by simp only [powMonoidHom_apply]; rw [← map_pow]⟩
      · rw [← hk, powMonoidHom_apply]
        exact MulEquiv.apply_symm_apply _ _
  have hidx : ((powMonoidHom p : (v.adicCompletionIntegers ℚ).unitGroup →*
        (v.adicCompletionIntegers ℚ).unitGroup).range).index
      = ((powMonoidHom p : (v.adicCompletionIntegers ℚ)ˣ →*
        (v.adicCompletionIntegers ℚ)ˣ).range).index := by
    rw [← he, Subgroup.index_map_equiv]
  calc Nat.card ((v.adicCompletionIntegers ℚ).unitGroup ⧸
        (powMonoidHom p : (v.adicCompletionIntegers ℚ).unitGroup →*
          (v.adicCompletionIntegers ℚ).unitGroup).range)
      = ((powMonoidHom p : (v.adicCompletionIntegers ℚ).unitGroup →*
          (v.adicCompletionIntegers ℚ).unitGroup).range).index := rfl
    _ = ((powMonoidHom p : (v.adicCompletionIntegers ℚ)ˣ →*
          (v.adicCompletionIntegers ℚ)ˣ).range).index := hidx
    _ = Nat.card ((v.adicCompletionIntegers ℚ)ˣ ⧸
          (powMonoidHom p : (v.adicCompletionIntegers ℚ)ˣ →*
            (v.adicCompletionIntegers ℚ)ˣ).range) := rfl
    _ = p := hA

theorem natCard_adicCompletion_units_rat_quot_pow
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (p : ℕ)
    (hp : p.Prime) (hodd : p ≠ 2)
    (hvalp : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((p:ℚ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (hres : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = p) :
    Nat.card ((v.adicCompletion ℚ)ˣ ⧸ (powMonoidHom p).range) = p ^ 2 := by
  have htor : ∀ h : Multiplicative ℤ, h ^ p = 1 → h = 1 := by
    intro h hh
    have h2 : Multiplicative.ofAdd ((p:ℤ) * Multiplicative.toAdd h) = 1 := by
      rw [← ofAdd_pow_eq (Multiplicative.toAdd h) p, ← ofAdd_toAdd h]
      exact hh
    have h3 : (p:ℤ) * Multiplicative.toAdd h = 0 := ofAdd_eq_one.mp h2
    have hp0 : (p:ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hm : Multiplicative.toAdd h = 0 := by
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 hp0
      · exact h4
    rw [← ofAdd_toAdd h, hm, ofAdd_zero]
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have htot := natCard_quot_powMonoidHom_eq_mul (unitsValLog (v.adicCompletion ℚ))
    (Commons.NumberTheory.NumberField.Completion.unitsValLog_adicCompletion_surjective ℚ v) p htor
  rw [htot, natCard_multiplicative_int_quot_pow p,
    natCard_ker_unitsValLog_quot_pow v p hp hodd hvalp hres]
  ring

/-! ## The main theorem -/

theorem natCard_powerQuotient_adicCompletion_rat_units {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hres : Nat.card (IsLocalRing.ResidueField
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)) = p) :
    Nat.card ((IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)ˣ ⧸
      (powMonoidHom p).range) = p ^ 2 := by
  have hgen : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p := by
    rw [← Commons.NumberTheory.NumberField.Set.absNorm_eq_primesEquiv v,
      ← Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm v]
    exact hres
  have hmem : (p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal :=
    Commons.NumberTheory.NumberField.mem_of_primesEquiv_eq v p hp (Subtype.ext hgen)
  have hvalp : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((p:ℚ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) :=
    Commons.NumberTheory.NumberField.Completion.val_prime_adicCompletion_rat hp v hmem
  exact natCard_adicCompletion_units_rat_quot_pow v p hp hodd hvalp hres

end
end Commons.NumberTheory.NumberField.Completion
