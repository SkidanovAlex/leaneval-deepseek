import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.subgroup_rayDegAux
import Submission.Work.BW.span_mono
import Submission.Work.BW.eval_conePt_mono
import Submission.Work.BW.eval_mono_eq_of_rowLat
import Submission.Work.BW.char_linearIndependent
import Submission.Work.BW.mono_mem_homPiece
import Submission.Work.BW.card_fib_true

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MvPolynomial

noncomputable section

/-!
# The Hilbert function of the closure of `G' = G_a × ker 𝒵`

We compute the dimension of the multidegree-`d` piece of the coordinate ring of the closure of
`G' = G_a × ker 𝒵` in `(P¹)^{N+1}` (i.e. of `MR N ⧸ subIdeal N ρ true M`, where
`𝒵 = rowLat N ρ M` is spanned by the rows of `M`).

The piece `homPiece N d` is spanned by the monomials `mono N d b` with `bᵢ ≤ dᵢ`; the monomial
`mono N d b` restricts to the function `(u, y) ↦ u^{b₀} · ∏ᵢ yᵢ^{bᵢ}` on `G'`.  Two such
monomials restrict to the same function exactly when `b₀ = b'₀` and the torus parts `(bᵢ)_{i≥1}`
differ by an element of `𝒵`; and monomials with pairwise different fibers are linearly independent
(separate the `u`-powers by a polynomial argument, then use Dedekind independence of the
characters of `ker 𝒵`).  Hence the graded piece has dimension equal to the number of fibers
realized by the exponent box, namely `(d 0 + 1) · boxClassCount`.
-/

/-- Elements of `subIdeal N ρ true M` vanish at the cone point over any point of
`G' = G_a × ker 𝒵`. -/
theorem subIdeal_vanish_true {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) {y : Fin (N + 1) → ℂ}
    (hy : InSub N ρ true M y) {F : MR N} (hF : F ∈ subIdeal N ρ true M) :
    MvPolynomial.eval (conePt N y) F = 0 := by
  have hle : subIdeal N ρ true M ≤ RingHom.ker (MvPolynomial.eval (conePt N y)) := by
    rw [subIdeal, Ideal.span_le]
    rintro G ⟨-, hGy⟩
    simpa using hGy y hy
  simpa using hle hF

/-- A polynomial in one variable over `ℂ` which vanishes identically has all coefficients zero. -/
theorem coeff_zero_of_sum_pow {n : ℕ} (a : Fin n → ℂ)
    (h : ∀ u : ℂ, ∑ k : Fin n, a k * u ^ (k : ℕ) = 0) : ∀ k, a k = 0 := by
  classical
  have hP : (∑ k : Fin n, Polynomial.C (a k) * Polynomial.X ^ (k : ℕ) : Polynomial ℂ) = 0 := by
    refine Polynomial.funext (fun u => ?_)
    rw [Polynomial.eval_finsetSum, Polynomial.eval_zero]
    rw [Finset.sum_congr rfl (fun k _ => by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X_pow])]
    exact h u
  intro k
  have hcoeff : (∑ j : Fin n, a j * (if (k : ℕ) = (j : ℕ) then 1 else 0)) = 0 := by
    have h1 : (Polynomial.lcoeff ℂ (k : ℕ))
        (∑ j : Fin n, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)) = 0 := by
      rw [hP, map_zero]
    rw [map_sum] at h1
    simpa only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] using h1
  rw [Finset.sum_eq_single k] at hcoeff
  · simpa using hcoeff
  · intro j _ hjk
    have hne : (k : ℕ) ≠ (j : ℕ) := fun hh => hjk (Fin.ext hh.symm)
    simp [hne]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- The generalisation of `char_linearIndependent` to an arbitrary finite index type. -/
theorem char_linearIndependent_fintype {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (hM : PrimSys M)
    {ι : Type*} [Fintype ι] (v : ι → Fin N → ℤ)
    (hv : ∀ i j, i ≠ j → ¬ ∃ c : Fin ρ → ℤ, ∀ m, v i m - v j m = ∑ r, c r * M r m)
    (cc : ι → ℂ)
    (h0 : ∀ y : Fin N → ℂ, (∀ i, y i ≠ 0) → (∀ j, ∏ i, y i ^ (M j i) = 1) →
        ∑ i, cc i * ∏ m, y m ^ (v i m) = 0) :
    ∀ i, cc i = 0 := by
  classical
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  set v' : Fin (Fintype.card ι) → Fin N → ℤ := fun j => v (e.symm j) with hv'
  set cc' : Fin (Fintype.card ι) → ℂ := fun j => cc (e.symm j) with hcc'
  have hv'eq : ∀ i j, i ≠ j →
      ¬ ∃ c : Fin ρ → ℤ, ∀ m, v' i m - v' j m = ∑ r, c r * M r m := by
    intro i j hij
    exact hv (e.symm i) (e.symm j) (fun h => hij (e.symm.injective h))
  have h0' : ∀ y : Fin N → ℂ, (∀ i, y i ≠ 0) → (∀ j, ∏ i, y i ^ (M j i) = 1) →
      ∑ i : Fin (Fintype.card ι), cc' i * ∏ m, y m ^ (v' i m) = 0 := by
    intro y hy hyk
    have hsum := Fintype.sum_equiv e (fun i : ι => cc i * ∏ m, y m ^ (v i m))
      (fun j : Fin (Fintype.card ι) => cc' j * ∏ m, y m ^ (v' j m))
      (fun i => by simp [hcc', hv'])
    rw [← hsum]
    exact h0 y hy hyk
  have hfin := char_linearIndependent M hM v' hv'eq cc' h0'
  intro i
  simpa [hcc', hv', he] using hfin (e i)

/-- Two monomials of multidegree `d` whose exponent vectors have the same `X_{0,1}`-exponent and
whose torus parts have the same class modulo `𝒵 = rowLat M` differ by an element of the vanishing
ideal `subIdeal N ρ true M`. -/
theorem mono_sub_mem_subIdeal_true {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    (b b' : Fin (N + 1) → ℕ) (hb : ∀ i, b i ≤ d i) (hb' : ∀ i, b' i ≤ d i)
    (h0 : b 0 = b' 0) (hcl : clsOf N ρ M (torPart b) = clsOf N ρ M (torPart b')) :
    mono N d b - mono N d b' ∈ subIdeal N ρ true M := by
  refine Ideal.subset_span ⟨⟨d, ?_⟩, ?_⟩
  · exact Submodule.sub_mem _ (mono_mem_homPiece N d b hb) (mono_mem_homPiece N d b' hb')
  · intro y hy
    have hrow : (fun i : Fin N => (b i.succ : ℤ)) - (fun i : Fin N => (b' i.succ : ℤ)) ∈
        rowLat N ρ M :=
      (Submodule.Quotient.eq (rowLat N ρ M)).mp hcl
    rw [map_sub, eval_mono_eq_of_rowLat M d b b' h0 hrow y hy.2.1 hy.2.2, sub_self]

/-- The value of `mono N d b` at the cone point over `(u, t)` (with `u` the `G_a`-coordinate and
`t` the torus coordinates). -/
theorem eval_mono_cons_torPart (N : ℕ) (d : Fin (N + 1) →₀ ℕ) (b : Fin (N + 1) → ℕ)
    (u : ℂ) (t : Fin N → ℂ) :
    MvPolynomial.eval (conePt N (Fin.cons u t)) (mono N d b)
      = u ^ (b 0) * ∏ m : Fin N, t m ^ (torPart b m) := by
  rw [eval_conePt_mono, Fin.prod_univ_succ, Fin.cons_zero]
  congr 1

/-- If a finite family of vectors of `V` is linearly independent modulo `I'` and its image spans
`V ⧸ I'`, then `V ⧸ I'` has dimension `Fintype.card ι`. -/
theorem finrank_quot_eq_card_of_fam {V : Type*} [AddCommGroup V] [Module ℂ V]
    (I' : Submodule ℂ V) {ι : Type*} [Fintype ι] (x : ι → V)
    (hind : ∀ g : ι → ℂ, (∑ i, g i • x i) ∈ I' → ∀ i, g i = 0)
    (hspan : ⊤ ≤ Submodule.span ℂ
      (Set.range (fun i => (Submodule.mkQ I') (x i)))) :
    Module.finrank ℂ (V ⧸ I') = Fintype.card ι := by
  have hi : LinearIndependent ℂ (fun i => (Submodule.mkQ I') (x i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : (Submodule.mkQ I') (∑ i, g i • x i)
        = ∑ i, g i • (Submodule.mkQ I') (x i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])
    have hker : (Submodule.mkQ I') (∑ i, g i • x i) = 0 := by rw [hsum, hg]
    have hg' : (∑ i, g i • x i) ∈ I' := by
      rw [← Submodule.ker_mkQ I']
      exact LinearMap.mem_ker.mpr hker
    exact hind g hg'
  exact Module.finrank_eq_card_basis (Module.Basis.mk hi hspan)

/-- Spanning a submodule by a family is the same as spanning it by the coerced family in the
ambient module. -/
theorem span_range_subtype_eq {M : Type*} [AddCommGroup M] [Module ℂ M] (p : Submodule ℂ M)
    {ι : Type*} (x : ι → p) (h : p = Submodule.span ℂ (Set.range fun i => (x i : M))) :
    (⊤ : Submodule ℂ p) = Submodule.span ℂ (Set.range x) := by
  refine le_antisymm ?_ le_top
  intro v _
  have hv : (v : M) ∈ Submodule.map (Submodule.subtype p) (Submodule.span ℂ (Set.range x)) := by
    rw [Submodule.map_span]
    have himg : (Submodule.subtype p) '' Set.range x = Set.range fun i => (x i : M) := by
      ext y
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨x i, ⟨i, rfl⟩, rfl⟩
    rw [himg, ← h]
    exact v.2
  rw [Submodule.mem_map] at hv
  obtain ⟨w, hw, hwv⟩ := hv
  have hwv' : w = v := Subtype.ext hwv
  rwa [hwv'] at hw

/-- Two elements of `homPiece N d` whose ambient difference lies in the vanishing ideal define the
same class modulo `I ⊓ homPiece N d`. -/
theorem mkQ_eq_of_sub_mem_subIdeal {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ)
    (M : Fin ρ → Fin N → ℤ) (u v : homPiece N d)
    (h : ((u : MR N)) - ((v : MR N)) ∈ subIdeal N ρ true M) :
    (Submodule.mkQ (Submodule.comap (homPiece N d).subtype
        ((subIdeal N ρ true M).restrictScalars ℂ))) u
      = (Submodule.mkQ (Submodule.comap (homPiece N d).subtype
        ((subIdeal N ρ true M).restrictScalars ℂ))) v := by
  have hmem : u - v ∈ Submodule.comap (homPiece N d).subtype
      ((subIdeal N ρ true M).restrictScalars ℂ) := by
    rw [Submodule.mem_comap]
    exact h
  have hzero : (Submodule.mkQ (Submodule.comap (homPiece N d).subtype
      ((subIdeal N ρ true M).restrictScalars ℂ))) (u - v) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hmem
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- The Hilbert function of the coordinate ring of the closure of `G' = G_a × ker 𝒵` in multidegree `d`: the ray section `(R/I)_d` has dimension `(d₀+1) · #(classes of the box ∏ᵢ[0,d_{i+1}] mod 𝒵)`.

The graded piece is `homPiece N d ⧸ (I ⊓ homPiece N d)` with `I = subIdeal N ρ true M`, i.e. `Submodule.comap (homPiece N d).subtype (I.restrictScalars ℂ)`.

Route (hints): every `F ∈ homPiece N d` lies in the span of the monomials `mono N d b` with `bᵢ ≤ dᵢ` (`span_mono`, import `Submission.Work.BW.span_mono` if available); monomials whose exponent vectors have the same fiber `(b 0, class of (bᵢ)_{i≥1} mod rowLat M)` define the same function on `ker M` (`eval_mono_eq_of_rowLat`); the functions of distinct fibers are linearly independent (group by the `X_{0,1}`-power and apply `char_linearIndependent` to the torus part, using that the monomials `y₀ ↦ y₀^k` are independent). Hence the quotient has dimension equal to the number of fibers realized in the box, namely `(d 0 + 1) * boxClassCount` (`card_fib_true`). -/
theorem finrank_subIdeal_true {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    (hM : PrimSys M) :
    Module.finrank ℂ (homPiece N d ⧸ Submodule.comap (homPiece N d).subtype
        ((subIdeal N ρ true M).restrictScalars ℂ))
      = (d 0 + 1) * boxClassCount N ρ M (fun i => d i.succ) := by
  classical
  -- ### The fibers realized by the exponent box
  set fibSet : Finset (ℕ × ((Fin N → ℤ) ⧸ rowLat N ρ M)) :=
    (degBox N d).image (fun b => (b 0, clsOf N ρ M (torPart b))) with hfibSet
  have hch : ∀ f : ↥fibSet, ∃ b : Fin (N + 1) → ℕ, b ∈ degBox N d ∧
      (b 0, clsOf N ρ M (torPart b)) = f.1 := fun f => Finset.mem_image.mp f.2
  set rep : ↥fibSet → Fin (N + 1) → ℕ := fun f => Classical.choose (hch f) with hrep
  have hrep_mem : ∀ f : ↥fibSet, rep f ∈ degBox N d :=
    fun f => (Classical.choose_spec (hch f)).1
  have hrep_fib : ∀ f : ↥fibSet, (rep f 0, clsOf N ρ M (torPart (rep f))) = f.1 :=
    fun f => (Classical.choose_spec (hch f)).2
  have hrep_le : ∀ f : ↥fibSet, ∀ i, rep f i ≤ d i :=
    fun f i => (mem_degBox d (rep f)).mp (hrep_mem f) i
  -- ### the representative monomials
  set xmonoK : ↥fibSet → homPiece N d :=
    fun f => ⟨mono N d (rep f), mono_mem_homPiece N d (rep f) (hrep_le f)⟩ with hxmonoK
  -- ### the graded piece
  set I' : Submodule ℂ (homPiece N d) :=
    Submodule.comap (homPiece N d).subtype ((subIdeal N ρ true M).restrictScalars ℂ) with hI'
  -- ### the `X_{0,1}`-exponent attached to a fiber
  have hklt : ∀ f : ↥fibSet, rep f 0 < d 0 + 1 :=
    fun f => Nat.lt_succ_of_le (hrep_le f 0)
  set kOf : ↥fibSet → Fin (d 0 + 1) := fun f => ⟨rep f 0, hklt f⟩ with hkOf
  have hkOf_val : ∀ f : ↥fibSet, (kOf f : ℕ) = rep f 0 := fun f => rfl
  -- ### independence of the representative monomials modulo `I'`
  have hind : ∀ g : ↥fibSet → ℂ, (∑ f, g f • xmonoK f) ∈ I' → ∀ f, g f = 0 := by
    intro g hg
    have hG : (∑ f, g f • mono N d (rep f)) ∈ subIdeal N ρ true M := by
      have hcoe : (homPiece N d).subtype (∑ f, g f • xmonoK f)
          = ∑ f, g f • mono N d (rep f) := by
        change ((∑ f, g f • xmonoK f : homPiece N d) : MR N)
          = ∑ f, g f • mono N d (rep f)
        rw [Submodule.coe_sum]
        refine Finset.sum_congr rfl (fun f _ => ?_)
        rw [Submodule.coe_smul, hxmonoK]
      rw [hI', Submodule.mem_comap] at hg
      rwa [hcoe] at hg
    -- evaluation at the points `y = (u, t)` of `G'`
    have key : ∀ t : Fin N → ℂ, (∀ i, t i ≠ 0) → (∀ j, ∏ i, t i ^ (M j i) = 1) →
        ∀ k : Fin (d 0 + 1),
          (∑ f ∈ Finset.univ.filter (fun f : ↥fibSet => kOf f = k),
            g f * ∏ m, t m ^ (torPart (rep f) m)) = 0 := by
      intro t ht hker k
      have hpoly : ∀ u : ℂ,
          (∑ k' : Fin (d 0 + 1),
            (∑ f ∈ Finset.univ.filter (fun f : ↥fibSet => kOf f = k'),
              g f * ∏ m, t m ^ (torPart (rep f) m)) * u ^ (k' : ℕ)) = 0 := by
        intro u
        set y : Fin (N + 1) → ℂ := Fin.cons u t with hy
        have hyIS : InSub N ρ true M y := by
          refine ⟨?_, ?_, ?_⟩
          · intro h
            exact absurd h (by decide)
          · intro i
            simpa [hy] using ht i
          · intro j
            simpa [hy] using hker j
        have h0 : MvPolynomial.eval (conePt N y) (∑ f, g f • mono N d (rep f)) = 0 :=
          subIdeal_vanish_true M hyIS hG
        have hev : MvPolynomial.eval (conePt N y) (∑ f, g f • mono N d (rep f))
            = ∑ f : ↥fibSet, g f * u ^ (rep f 0) * ∏ m, t m ^ (torPart (rep f) m) := by
          rw [map_sum]
          refine Finset.sum_congr rfl (fun f _ => ?_)
          rw [MvPolynomial.smul_eval, hy, eval_mono_cons_torPart]
          ring
        rw [hev] at h0
        have hgroup : (∑ k' : Fin (d 0 + 1),
              (∑ f ∈ Finset.univ.filter (fun f : ↥fibSet => kOf f = k'),
                g f * ∏ m, t m ^ (torPart (rep f) m)) * u ^ (k' : ℕ))
            = ∑ f : ↥fibSet, g f * u ^ (rep f 0) *
                ∏ m, t m ^ (torPart (rep f) m) := by
          rw [← Finset.sum_fiberwise (s := Finset.univ) (g := kOf)
            (f := fun f : ↥fibSet => g f * u ^ (rep f 0) *
              ∏ m, t m ^ (torPart (rep f) m))]
          refine Finset.sum_congr rfl (fun k' _ => ?_)
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun f hf => ?_)
          have hk : rep f 0 = (k' : ℕ) := by
            rw [← hkOf_val f]
            exact congrArg Fin.val (Finset.mem_filter.mp hf).2
          rw [hk]
          ring
        rw [hgroup]
        exact h0
      exact coeff_zero_of_sum_pow (fun k' : Fin (d 0 + 1) =>
        ∑ f ∈ Finset.univ.filter (fun f : ↥fibSet => kOf f = k'),
          g f * ∏ m, t m ^ (torPart (rep f) m)) hpoly k
    -- ### separate the `X_{0,1}`-block by Dedekind independence of the torus characters
    have hblock : ∀ k : Fin (d 0 + 1), ∀ f : ↥fibSet, kOf f = k → g f = 0 := by
      intro k f0 hf0
      have hcc : ∀ i : {f : ↥fibSet // kOf f = k}, g i.1 = 0 := by
        refine char_linearIndependent_fintype M hM
          (fun i : {f : ↥fibSet // kOf f = k} => torPart (rep i.1)) ?_ (fun i => g i.1) ?_
        · intro i j hij hcon
          obtain ⟨c, hc⟩ := hcon
          have hmem : torPart (rep i.1) - torPart (rep j.1) ∈ rowLat N ρ M := by
            have hfun : torPart (rep i.1) - torPart (rep j.1) = ∑ r, c r • M r := by
              funext m
              simpa using hc m
            rw [hfun]
            exact Submodule.sum_mem _ (fun r _ =>
              Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self r)))
          have hcls : clsOf N ρ M (torPart (rep i.1)) = clsOf N ρ M (torPart (rep j.1)) :=
            (Submodule.Quotient.eq (rowLat N ρ M)).mpr hmem
          have hfj : i.1 = j.1 := by
            refine Subtype.ext ?_
            rw [← hrep_fib i.1, ← hrep_fib j.1]
            refine Prod.ext ?_ hcls
            have h1 : (kOf i.1 : ℕ) = (kOf j.1 : ℕ) := by rw [i.2, j.2]
            rw [← hkOf_val i.1, ← hkOf_val j.1]
            exact h1
          exact hij (Subtype.ext hfj)
        · intro y hy hyk
          have hk0 := key y hy hyk k
          rw [← hk0]
          exact (Finset.sum_subtype
            (s := Finset.univ.filter (fun f : ↥fibSet => kOf f = k))
            (p := fun f : ↥fibSet => kOf f = k)
            (fun x => by simp)
            (fun f => g f * ∏ m, y m ^ (torPart (rep f) m))).symm
      exact hcc ⟨f0, hf0⟩
    intro f0
    exact hblock (kOf f0) f0 rfl
  -- ### the representative monomials span modulo `I'`
  have hspan : ⊤ ≤ Submodule.span ℂ
      (Set.range (fun f : ↥fibSet => (Submodule.mkQ I') (xmonoK f))) := by
    set g0 : {b : Fin (N + 1) → ℕ // ∀ i, b i ≤ d i} → ↥fibSet :=
      fun b => ⟨(b.1 0, clsOf N ρ M (torPart b.1)),
        Finset.mem_image.mpr ⟨b.1, (mem_degBox d b.1).mpr b.2, rfl⟩⟩ with hg0
    set xb : {b : Fin (N + 1) → ℕ // ∀ i, b i ≤ d i} → homPiece N d :=
      fun b => ⟨mono N d b.1, mono_mem_homPiece N d b.1 b.2⟩ with hxb
    -- the monomials of the box span `homPiece N d`
    have htop : (⊤ : Submodule ℂ (homPiece N d)) = Submodule.span ℂ (Set.range xb) :=
      span_range_subtype_eq (homPiece N d) xb (span_mono N d)
    -- congruent modulo `I'` to the representative monomial of the same fiber
    have hcong : ∀ b : {b : Fin (N + 1) → ℕ // ∀ i, b i ≤ d i},
        (Submodule.mkQ I') (xb b) = (Submodule.mkQ I') (xmonoK (g0 b)) := by
      intro b
      have h0b : b.1 0 = rep (g0 b) 0 := (congrArg Prod.fst (hrep_fib (g0 b))).symm
      have hclb : clsOf N ρ M (torPart b.1) = clsOf N ρ M (torPart (rep (g0 b))) :=
        (congrArg Prod.snd (hrep_fib (g0 b))).symm
      have hmem_amb : ((xb b : MR N)) - ((xmonoK (g0 b) : homPiece N d) : MR N)
          ∈ subIdeal N ρ true M := by
        rw [hxb, hxmonoK]
        simpa using mono_sub_mem_subIdeal_true d M b.1 (rep (g0 b)) b.2 (hrep_le (g0 b)) h0b hclb
      exact mkQ_eq_of_sub_mem_subIdeal d M (xb b) (xmonoK (g0 b)) hmem_amb
    have hmap : Submodule.map (Submodule.mkQ I') (⊤ : Submodule ℂ (homPiece N d)) ≤
        Submodule.span ℂ (Set.range (fun f : ↥fibSet => (Submodule.mkQ I') (xmonoK f))) := by
      rw [htop, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
      rw [hcong b]
      exact Submodule.subset_span (Set.mem_range_self (g0 b))
    have htopQ : Submodule.map (Submodule.mkQ I') (⊤ : Submodule ℂ (homPiece N d)) = ⊤ := by
      rw [Submodule.map_top, LinearMap.range_eq_top]
      exact Submodule.mkQ_surjective I'
    rwa [htopQ] at hmap
  -- ### assembly
  have hfin := finrank_quot_eq_card_of_fam I' xmonoK hind hspan
  have hcard0 : Fintype.card ↥fibSet = fibSet.card := Fintype.card_coe fibSet
  have hcard1 : fibSet.card = fibImg N ρ d M := by rw [hfibSet]; rfl
  rw [hfin, hcard0, hcard1]
  exact card_fib_true d M

end

end Work.BW
