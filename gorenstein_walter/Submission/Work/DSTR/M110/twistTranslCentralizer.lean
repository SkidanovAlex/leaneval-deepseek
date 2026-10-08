import Mathlib
import Submission.Work.DSTR.M110.Defs
import Submission.Work.DSTR.M110.Galois.decomposition
import Submission.Work.DSTR.M110.SplitCase.GaloisPart
import Submission.Work.DSTR.M110.SplitCase.PglCentralizer
import Submission.Work.DSTR.M110.frobeniusRingAut
import Submission.Work.DSTR.M110.Mobius
import Submission.Work.DSTR.M110.Normalizer.Defs
import Submission.Work.DSTR.M110.twistAux.twistAuxAffineConjTransl
import Submission.Work.DSTR.M110.twistAux.twistAuxExistsFixedOfNormOne
import Submission.Work.DSTR.M110.twistAux.twistAuxEqOneOfFixesFixedField
import Submission.Work.DSTR.M110.twistAux.twistAuxOrderTwoAffineNorm

/-!
# The centralizer of a twisted involution inside the translation group

Let `F = GF(p^k)` (`p` odd, `p^k ≥ 5`) and let `t ∈ PΓL(2,F)` be an involution fixing `∞`
with `t ∉ PGL(2,F)` (a *twist*).  Then `t` acts on the finite points by `z ↦ a·σ(z) + b`,
where `σ = galPart t` is the order-two field automorphism and `a·σ(a) = 1`.  The translations
commuting with `t` are therefore the `transl d` with `a·σ(d) = d`; that set is non-empty by the
twisted-trace trick `twistAuxExistsFixedOfNormOne`.

The lemma proved here: if `x ∈ PΓL(2,F)` has **odd order** and centralizes every translation
`transl d` that is centralized by `t`, then `x ∈ PGL(2,F)`.

Proof.  `x` centralizes some `transl d₀` with `d₀ ≠ 0`, hence fixes `∞` (the unique fixed point
of a nontrivial translation) and has an affine description `z ↦ A·τ(z) + B` with Galois part
`τ = galPart x`.  Comparing the two conjugation formulae gives `A·τ(d) = d` for every `d` with
`a·σ(d) = d`; multiplying such a `d` by an element of the fixed field `Fix σ` and comparing
with `d₀` shows that `τ` fixes `Fix σ` pointwise.  Finally `Fix σ ⊆ Fix τ` forces
`orderOf τ ∣ 2` (the degree of a fixed field equals the order of the automorphism group), while
`orderOf τ` is odd; so `τ = 1` and `x ∈ PGL`.
-/

open OnePoint
open scoped MatrixGroups LinearAlgebra.Projectivization

namespace Work.DSTR.M110

/-! ## Two elementary conjugation formulae -/

/-- A field automorphism conjugates the translation `x ↦ x + d` into the translation
`x ↦ x + σ d`. -/
private lemma galHom_mul_transl_aux (F : Type*) [Field F] [DecidableEq F] (σ : F ≃+* F) (d : F) :
    Work.AUTL2.galHom F σ * Work.AUTL2.transl F d =
      Work.AUTL2.transl F (σ d) * Work.AUTL2.galHom F σ := by
  rw [Equiv.ext_iff, OnePoint.forall]
  refine ⟨?_, fun z => ?_⟩
  · simp only [Equiv.Perm.mul_apply, Work.AUTL2.transl_infty,
      Work.AUTL2.Normalizer.galHom_apply_infty]
  · simp only [Equiv.Perm.mul_apply, Work.AUTL2.transl_formula,
      Work.AUTL2.Normalizer.galHom_apply_coe, map_add]

/-- An element `y = c * galHom σ` of `PΓL(2,F)` whose `PGL`-part `c` is affine
`z ↦ α z + β` conjugates `transl d` into `transl (α * σ d)`. -/
private lemma conjTransl_of_decomp (F : Type*) [Field F] [DecidableEq F]
    (y c : Equiv.Perm (Work.AUTL2.P1 F)) (σ : F ≃+* F) (α β : F)
    (hy : y = c * Work.AUTL2.galHom F σ)
    (hinf : c OnePoint.infty = OnePoint.infty)
    (haff : ∀ z : F, c (z : Work.AUTL2.P1 F) = ((α * z + β : F) : Work.AUTL2.P1 F)) :
    ∀ d : F, y * Work.AUTL2.transl F d = Work.AUTL2.transl F (α * σ d) * y := by
  intro d
  calc y * Work.AUTL2.transl F d
      = (c * Work.AUTL2.galHom F σ) * Work.AUTL2.transl F d := by rw [hy]
    _ = c * (Work.AUTL2.galHom F σ * Work.AUTL2.transl F d) := by rw [mul_assoc]
    _ = c * (Work.AUTL2.transl F (σ d) * Work.AUTL2.galHom F σ) := by
          rw [galHom_mul_transl_aux F σ d]
    _ = (c * Work.AUTL2.transl F (σ d)) * Work.AUTL2.galHom F σ := by rw [mul_assoc]
    _ = (Work.AUTL2.transl F (α * σ d) * c) * Work.AUTL2.galHom F σ := by
          rw [twistAuxAffineConjTransl F c (σ d) hinf α β haff]
    _ = Work.AUTL2.transl F (α * σ d) * (c * Work.AUTL2.galHom F σ) := by rw [mul_assoc]
    _ = Work.AUTL2.transl F (α * σ d) * y := by rw [hy]

/-! ## Formula-level facts about `galPart` -/

/-- The `m`-th power of `galPart F ⟨y, hy⟩` is trivial whenever the `m`-th power of `y` is. -/
private lemma galPart_pow_of_pow (F : Type*) [Field F] [DecidableEq F]
    (y : Equiv.Perm (Work.AUTL2.P1 F)) (hy : y ∈ Work.AUTL2.pgammaL F) (m : ℕ)
    (hm : y ^ m = 1) :
    (SplitAux.galPart F ⟨y, hy⟩) ^ m = 1 := by
  have hY : (⟨y, hy⟩ : ↥(Work.AUTL2.pgammaL F)) ^ m = 1 := by
    apply Subtype.ext
    simpa using hm
  have h := congrArg (SplitAux.galMap F) hY
  rw [map_pow, map_one] at h
  simpa [SplitAux.galMap_apply] using h

/-- **Structure of an element of `PΓL(2,F)` fixing `∞`.**  Such an element `y` has Galois part
`σ = galPart y`, acts on the finite points by an affine map `z ↦ α z + β` composed with `σ`,
and conjugates `transl d` into `transl (α * σ d)`. -/
private lemma pgammaL_fixes_infty_affine_gal (F : Type*) [Field F] [DecidableEq F]
    (y : Equiv.Perm (Work.AUTL2.P1 F)) (hy : y ∈ Work.AUTL2.pgammaL F)
    (hinf : y OnePoint.infty = OnePoint.infty) :
    ∃ (σ : F ≃+* F) (α β : F), α ≠ 0 ∧ σ = SplitAux.galPart F ⟨y, hy⟩ ∧
      (∀ z : F, y (z : Work.AUTL2.P1 F) = ((α * σ z + β : F) : Work.AUTL2.P1 F)) ∧
      (∀ d : F, y * Work.AUTL2.transl F d = Work.AUTL2.transl F (α * σ d) * y) := by
  obtain ⟨c, hc, hcy⟩ := SplitAux.galPart_spec F ⟨y, hy⟩
  set σ : F ≃+* F := SplitAux.galPart F ⟨y, hy⟩ with hσdef
  have hcy' : y = c * Work.AUTL2.galHom F σ := by simpa [hσdef] using hcy
  have hcinf : c OnePoint.infty = OnePoint.infty := by
    have h := hinf
    rw [hcy', Equiv.Perm.mul_apply, Work.AUTL2.Normalizer.galHom_apply_infty] at h
    exact h
  obtain ⟨α, β, hα, haff⟩ := SplitAux.pglImage_fixing_infty F c hc hcinf
  refine ⟨σ, α, β, hα, hσdef, ?_, ?_⟩
  · intro z
    have h := haff (σ z)
    calc y (z : Work.AUTL2.P1 F)
        = (c * Work.AUTL2.galHom F σ) (z : Work.AUTL2.P1 F) := by rw [hcy']
      _ = c (Work.AUTL2.galHom F σ (z : Work.AUTL2.P1 F)) := by rw [Equiv.Perm.mul_apply]
      _ = c ((σ z : F) : Work.AUTL2.P1 F) := by rw [Work.AUTL2.Normalizer.galHom_apply_coe]
      _ = ((α * σ z + β : F) : Work.AUTL2.P1 F) := h
  · intro d
    exact conjTransl_of_decomp F y c σ α β hcy' hcinf haff d

/-! ## The main theorem -/

theorem twistTranslCentralizer (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    [DecidableEq (GaloisField p k)] (t x : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))
    (htG : t ∈ Work.AUTL2.pgammaL (GaloisField p k))
    (htinf : t OnePoint.infty = OnePoint.infty)
    (ht2 : orderOf t = 2) (htnpgl : t ∉ Work.AUTL2.pglImage (GaloisField p k))
    (hx : x ∈ Work.AUTL2.pgammaL (GaloisField p k)) (hodd : Odd (orderOf x))
    (hcomm : ∀ c : GaloisField p k, Work.AUTL2.transl (GaloisField p k) c * t = t * Work.AUTL2.transl (GaloisField p k) c →
        x * Work.AUTL2.transl (GaloisField p k) c = Work.AUTL2.transl (GaloisField p k) c * x) :
    x ∈ Work.AUTL2.pglImage (GaloisField p k) := by
  classical
  have hk : k ≠ 0 := by rintro rfl; simp at hq
  -- `t` is an involution
  have ht2' : t * t = 1 := by simpa [ht2, pow_two] using pow_orderOf_eq_one t
  -- structure of `t`: `t z = a * σt z + b`, and `t * transl d = transl (a * σt d) * t`
  obtain ⟨σt, a, b, ha, hσt_eq, ht_aff, ht_conj⟩ :=
    pgammaL_fixes_infty_affine_gal (GaloisField p k) t htG htinf
  have hσt_ne : σt ≠ 1 := by
    intro h
    refine htnpgl ?_
    have h1 : SplitAux.galPart (GaloisField p k) ⟨t, htG⟩ = 1 := by rw [← hσt_eq]; exact h
    exact (SplitAux.galPart_eq_one_iff (GaloisField p k) ⟨t, htG⟩).mp h1
  have hσt_sq : σt ^ 2 = 1 := by
    rw [hσt_eq]
    exact galPart_pow_of_pow (GaloisField p k) t htG 2 ht2'
  have hσt_ord : orderOf σt = 2 := orderOf_eq_prime hσt_sq hσt_ne
  -- the multiplier of `t` has norm one
  have hta : a * σt a = 1 :=
    Work.DSTR.M110.twistAux.twistAuxOrderTwoAffineNorm (GaloisField p k) σt a b t ht_aff ht2'
  -- a nonzero fixed point of `d ↦ a * σt d`
  have hσt_mul : σt * σt = 1 := by rw [← pow_two]; exact hσt_sq
  obtain ⟨d0, hd0ne, hd0⟩ :=
    Work.DSTR.M110.twistAux.twistAuxExistsFixedOfNormOne (GaloisField p k) σt hσt_mul hσt_ne a hta
  -- `x` commutes with every translation centralizing `t`
  have hx_comm : ∀ d : GaloisField p k, a * σt d = d →
      x * Work.AUTL2.transl (GaloisField p k) d =
        Work.AUTL2.transl (GaloisField p k) d * x := by
    intro d hd
    refine hcomm d ?_
    rw [ht_conj d, hd]
  -- hence `x` fixes the unique fixed point `∞` of `transl d₀`
  have hxinf : x OnePoint.infty = OnePoint.infty := by
    have h := congrFun (congrArg DFunLike.coe (hx_comm d0 hd0)) OnePoint.infty
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Work.AUTL2.transl_infty] at h
    exact Work.AUTL2.transl_fixed (GaloisField p k) d0 hd0ne (x OnePoint.infty) h.symm
  -- structure of `x`
  obtain ⟨σx, A, B, hA, hσx_eq, hx_aff, hx_conj⟩ :=
    pgammaL_fixes_infty_affine_gal (GaloisField p k) x hx hxinf
  -- `A * σx d = d` for every `d` centralized by `t`
  have hA_fix : ∀ d : GaloisField p k, a * σt d = d → A * σx d = d := by
    intro d hd
    have h1 : Work.AUTL2.transl (GaloisField p k) (A * σx d) * x =
        Work.AUTL2.transl (GaloisField p k) d * x := by
      rw [← hx_conj d, hx_comm d hd]
    exact Work.AUTL2.Normalizer.transl_injective (GaloisField p k) (mul_right_cancel h1)
  -- consequently `σx` fixes the whole fixed field of `σt` pointwise
  have hσx_fix : ∀ m : GaloisField p k, σt m = m → σx m = m := by
    intro m hm
    have h1 : a * σt (d0 * m) = d0 * m := by
      rw [map_mul, hm, ← mul_assoc, hd0]
    have h2 : A * σx (d0 * m) = d0 * m := hA_fix _ h1
    have h3 : A * σx d0 = d0 := hA_fix d0 hd0
    rw [map_mul] at h2
    have h4 : A * σx d0 * σx m = d0 * m := by rw [mul_assoc]; exact h2
    rw [h3] at h4
    exact mul_left_cancel₀ hd0ne h4
  -- `σx` has odd order
  have hσx_odd : Odd (orderOf σx) := by
    have hdvd : orderOf σx ∣ orderOf x := by
      rw [orderOf_dvd_iff_pow_eq_one, hσx_eq]
      exact galPart_pow_of_pow (GaloisField p k) x hx (orderOf x) (pow_orderOf_eq_one x)
    exact Odd.of_dvd_nat hodd hdvd
  -- the degree argument forces `σx = 1`
  have hσx_one : σx = 1 :=
    Work.DSTR.M110.twistAux.twistAuxEqOneOfFixesFixedField p k hk σt σx hσt_ord hσx_odd hσx_fix
  have hgal : SplitAux.galPart (GaloisField p k) ⟨x, hx⟩ = 1 := by
    rw [← hσx_eq]; exact hσx_one
  exact (SplitAux.galPart_eq_one_iff (GaloisField p k) ⟨x, hx⟩).mp hgal

end Work.DSTR.M110
