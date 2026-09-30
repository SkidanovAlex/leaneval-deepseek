import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.moduleFinite_homPiece
import Submission.Work.BW.rayHilb_cut_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MvPolynomial

/-- Dimension count for the "cut" sequence. If `K ≤ B` is the preimage under `f : B →ₗ A` of a
subspace `S ≤ A`, then cutting `A` by `S` and then by the image of `f` accounts for the whole of
`A ⧸ S`, the loss being exactly the quotient `B ⧸ K`:

`dim (A ⧸ S) = dim (A ⧸ (S ⊔ f.range)) + dim (B ⧸ K)`.

(Equivalently, `f` induces an isomorphism `B ⧸ K ≅ (S ⊔ f.range) ⧸ S`, and the third isomorphism
theorem identifies `(A ⧸ S) ⧸ ((S ⊔ f.range) ⧸ S)` with `A ⧸ (S ⊔ f.range)`.) -/
private theorem finrank_quot_comap {𝕜 : Type*} [Field 𝕜] {A : Type*} [AddCommGroup A]
    [Module 𝕜 A] [FiniteDimensional 𝕜 A] {B : Type*} [AddCommGroup B] [Module 𝕜 B]
    [FiniteDimensional 𝕜 B] (f : B →ₗ[𝕜] A) (S : Submodule 𝕜 A) (K : Submodule 𝕜 B)
    (hK : Submodule.comap f S = K) :
    Module.finrank 𝕜 (A ⧸ S) =
      Module.finrank 𝕜 (A ⧸ (S ⊔ LinearMap.range f)) + Module.finrank 𝕜 (B ⧸ K) := by
  have hker : (S.mkQ.comp f).ker = K := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, hK]
  have hrange : (S.mkQ.comp f).range = Submodule.map S.mkQ (LinearMap.range f) :=
    LinearMap.range_comp f S.mkQ
  have h1 : Module.finrank 𝕜 ((S.mkQ.comp f).range) + Module.finrank 𝕜 K
      = Module.finrank 𝕜 B := by
    rw [← hker]; exact LinearMap.finrank_range_add_finrank_ker _
  have h2 : Module.finrank 𝕜 (B ⧸ K) + Module.finrank 𝕜 K = Module.finrank 𝕜 B :=
    Submodule.finrank_quotient_add_finrank K
  have hm : Module.finrank 𝕜 (Submodule.map S.mkQ (LinearMap.range f))
      = Module.finrank 𝕜 (B ⧸ K) := by
    rw [← hrange]; omega
  have h4 : Module.finrank 𝕜 ((A ⧸ S) ⧸ Submodule.map S.mkQ (LinearMap.range f))
      + Module.finrank 𝕜 (Submodule.map S.mkQ (LinearMap.range f))
      = Module.finrank 𝕜 (A ⧸ S) := Submodule.finrank_quotient_add_finrank _
  have h5 : Module.finrank 𝕜 ((A ⧸ S) ⧸ Submodule.map S.mkQ (LinearMap.range f))
      = Module.finrank 𝕜 (A ⧸ (S ⊔ LinearMap.range f)) :=
    (Submodule.quotientQuotientEquivQuotientSup S (LinearMap.range f)).finrank_eq
  rw [h5, hm] at h4
  omega

/-- Philippon 3.1 along the ray `D`. If `I` is multihomogeneous and `Q` is a multihomogeneous
element of multidegree `k • D` (`k ≥ 1`) which is a non-zerodivisor modulo `I`, then
`(R/I)_{tD} →·Q (R/I)_{(t+k)D} → (R/(I,Q))_{(t+k)D} → 0` is exact, so the ray Hilbert functions
satisfy `rayHilb I (t+k) = rayHilb (I ⊔ (Q)) (t+k) + rayHilb I t` for every `t`.

Notes for the prover.
* You will need `Module.Finite ℂ ↥(homPiece N m)` for the `finrank` lemmas
  (`Submodule.finrank_quotient_add_finrank`, `Submodule.finrank_sup_add_finrank_inf_eq`); this is
  provable locally (as a `haveI`) e.g. by reducing to total degree: `homPiece N m ≤` the total-degree
  piece of degree `∑ i, (m • D) i`, which is finitely generated
  (`MvPolynomial.homogeneousSubmodule_fg`), or from
  `MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported`, `MvPolynomial.basisRestrictSupport`
  and the finiteness of `{m | Finsupp.weight (mdeg N) m = d}` (the constraint forces `m v ≤ d v.1`).
* Suggested module-theoretic identity to prove first, for `m := t + k`:
  `(I ⊔ Ideal.span {Q}) ⊓ homPiece N (m • D) = (I ⊓ homPiece N (m • D)) ⊔ (homPiece N ((m - k) • D)).map (LinearMap.mulLeft ℂ Q)`.
  The `⊆` inclusion uses `MultiHom N I` together with `weightedHomogeneousComponent` (write
  `y = i + q * Q` and project to multidegree `m • D`; the component of `q * Q` at `m • D` is the
  component of `q` at `(m-k) • D` times `Q`, all other components vanishing because `Q` is
  homogeneous of multidegree `k • D`).
* The `finrank` count then follows since `x ↦ Q * x` is injective (from `hreg`) and maps
  `I ⊓ homPiece N ((m-k) • D)` onto `(I ⊓ homPiece N (m • D)) ⊓ (homPiece N ((m-k) • D)).map (mulLeft Q)`.
  (`(m - k) • D = t • D` because `hk : 1 ≤ k`.) -/
theorem rayHilb_cut {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (k : ℕ) (hk : 1 ≤ k) (I : Ideal (MR N))
    (hI : MultiHom N I) (Q : MR N) (hQ : Q ∈ homPiece N (k • D))
    (hreg : ∀ f, Q * f ∈ I → f ∈ I) (t : ℕ) :
    rayHilb N D I (t + k) = rayHilb N D (I ⊔ Ideal.span {Q}) (t + k) + rayHilb N D I t := by
  -- `A` and `B` are the two graded pieces meeting in the "cut" exact sequence;
  -- `S`, `K` are the degree-`(t+k)D` and degree-`tD` parts of `I`.
  let A := homPiece N ((t + k) • D)
  let B := homPiece N (t • D)
  let S : Submodule ℂ A := Submodule.comap A.subtype (I.restrictScalars ℂ)
  let K : Submodule ℂ B := Submodule.comap B.subtype (I.restrictScalars ℂ)
  haveI hAfin : FiniteDimensional ℂ A := moduleFinite_homPiece N ((t + k) • D)
  haveI hBfin : FiniteDimensional ℂ B := moduleFinite_homPiece N (t • D)
  have memS : ∀ x : A, x ∈ S ↔ (x : MR N) ∈ I := by
    intro x; simp only [S, Submodule.mem_comap]; exact Iff.rfl
  have memK : ∀ x : B, x ∈ K ↔ (x : MR N) ∈ I := by
    intro x; simp only [K, Submodule.mem_comap]; exact Iff.rfl
  -- Multiplication by `Q` is injective modulo `I`: its kernel is `K`.
  have hcomap : Submodule.comap (mulQ D k Q hQ t) S = K := by
    ext x
    rw [Submodule.mem_comap, memS (mulQ D k Q hQ t x), memK x, mulQ_apply]
    exact ⟨fun h => hreg x.1 h, fun h => Ideal.mul_mem_left I Q h⟩
  -- The degree-`(t+k)D` part of `(I, Q)` is the part of `I` together with `Q · (tD)`.
  have hcut : S ⊔ (mulQ D k Q hQ t).range
      = Submodule.comap A.subtype ((I ⊔ Ideal.span {Q}).restrictScalars ℂ) := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · intro y hy
        rw [Submodule.mem_comap] at hy ⊢
        exact Ideal.mem_sup_left hy
      · rintro y ⟨x, rfl⟩
        rw [Submodule.mem_comap]
        show (mulQ D k Q hQ t x : MR N) ∈ I ⊔ Ideal.span {Q}
        rw [mulQ_apply]
        exact Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr ⟨x.1, rfl⟩)
    · intro y hy
      rw [Submodule.mem_comap] at hy
      have hy' : (y : MR N) ∈ I ⊔ Ideal.span {Q} := hy
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy'
      rw [Ideal.mem_span_singleton, dvd_def] at hb
      obtain ⟨c, hc⟩ := hb
      have hy2 : (y : MR N) = a + Q * c := by rw [← hab, hc]
      have hycomp : weightedHomogeneousComponent (mdeg N) ((t + k) • D) (y : MR N)
          = (y : MR N) := by
        have := (mem_weightedHomogeneousSubmodule ℂ (mdeg N) ((t + k) • D) (y : MR N)).mp y.2
        exact IsWeightedHomogeneous.weightedHomogeneousComponent_same this
      have hcomp : weightedHomogeneousComponent (mdeg N) ((t + k) • D) (a + Q * c)
          = weightedHomogeneousComponent (mdeg N) ((t + k) • D) a
            + weightedHomogeneousComponent (mdeg N) (t • D) c * Q := by
        rw [map_add]
        congr 1
        rw [add_smul, mul_comm Q c, mul_whc_cut Q hQ c (t • D)]
      have key : (y : MR N) = weightedHomogeneousComponent (mdeg N) ((t + k) • D) a
          + weightedHomogeneousComponent (mdeg N) (t • D) c * Q := by
        rw [← hycomp, hy2, hcomp]
      have ha_mem : weightedHomogeneousComponent (mdeg N) ((t + k) • D) a ∈ I :=
        hI a ha ((t + k) • D)
      have hc_mem : weightedHomogeneousComponent (mdeg N) (t • D) c ∈ homPiece N (t • D) :=
        weightedHomogeneousComponent_mem (mdeg N) c (t • D)
      have hca_mem : weightedHomogeneousComponent (mdeg N) ((t + k) • D) a ∈ A :=
        weightedHomogeneousComponent_mem (mdeg N) a ((t + k) • D)
      refine Submodule.mem_sup.mpr
        ⟨⟨weightedHomogeneousComponent (mdeg N) ((t + k) • D) a, hca_mem⟩, (memS _).mpr ha_mem,
         mulQ D k Q hQ t ⟨weightedHomogeneousComponent (mdeg N) (t • D) c, hc_mem⟩,
         ⟨⟨_, hc_mem⟩, rfl⟩, ?_⟩
      apply Subtype.ext
      rw [key]
      simp only [Submodule.coe_add, mulQ_apply]
      rw [mul_comm Q]
  -- The dimension count: `dim (A/S) = dim (A/(S + Q·B)) + dim (B/K)`.
  have hkey := finrank_quot_comap (mulQ D k Q hQ t) S K hcomap
  rw [hcut] at hkey
  exact hkey

end Work.BW
