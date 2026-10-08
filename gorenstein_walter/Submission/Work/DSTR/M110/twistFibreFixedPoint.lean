import Mathlib
import Submission.Work.DSTR.M110.twistBasics
import Submission.Work.DSTR.M110.Defs
import Submission.Work.DSTR.M110.Normalizer.Defs
import Submission.Work.DSTR.M110.Mobius
import Submission.Work.DSTR.M110.SplitCase.GaloisPart

/-!
# The twist fibre fixed point (DS10a, twist case)

`twistFibreFixedPoint`: let `Q` satisfy `PSL(2,q) ≤ Q ≤ PΓL(2,q)` (`q = p^k`, `p` odd, `q ≥ 5`),
let `t ∈ Q` fix `∞`, and let `N ≤ Q` be an `r`-subgroup (`r` odd, `r ≠ p`) contained in `C_Q(t)`
and normalised by `C_Q(t)`.  If `x ∈ N` does not lie in `PGL(2,q)`, then some `y ∈ N` does not lie
in `PGL(2,q)` either and commutes with every translation `z ↦ z + c` commuting with `t`.

This is the fibre argument of the twist case of DS10a.  The Galois part `ψ` of an element of
`PΓL(2,q)` (the projection `PΓL(2,q) →* Aut F` with kernel `PGL(2,q)`) restricted to `N` is a
homomorphism whose kernel is `N ∩ PGL(2,q)`, so the `ψ`-fibre `Ω` of `x` has cardinality
`|N ∩ PGL(2,q)|`, which divides the `r`-power `|N|` and hence is coprime to `p`.  The group `V` of
translations centralising `t` is a `p`-group (the additive group of `F`), it acts by conjugation on
`Ω`, and `V` preserves `ψ` (being contained in `PSL(2,q) ≤ PGL(2,q)`), so `Ω` is a `V`-set with
cardinality coprime to `p`: it has a fixed point `y`.  Then `ψ y = ψ x ≠ 1`, so `y ∉ PGL(2,q)`, and
every translation `z ↦ z + c` with `transl c * t = t * transl c` centralises `y`.
-/

namespace Work.DSTR.M110

open Work.AUTL2

/-- **Cardinality of a fibre of a homomorphism.**  Let `ψ : ↥N →* H` be a homomorphism on a
subgroup `N ≤ G` whose kernel is `N ∩ P`, where `P ≤ G`.  Then the fibre of `ψ` through any
`x : ↥N` has the cardinality of `N ∩ P` (translation by `x⁻¹` is a bijection onto `N ∩ ker ψ`). -/
lemma card_fibre_eq_card_inf_ker {G H : Type*} [Group G] [Group H] (N P : Subgroup G)
    (ψ : ↥N →* H) (hker : ∀ y : ↥N, ψ y = 1 ↔ ((y : G) ∈ P)) (x : ↥N) :
    Nat.card {y : ↥N // ψ y = ψ x} = Nat.card ↥(N ⊓ P) := by
  refine Nat.card_congr ⟨?_, ?_, ?_, ?_⟩
  · intro y
    refine ⟨(x⁻¹ * y.1 : ↥N), ⟨(x⁻¹ * y.1 : ↥N).2, ?_⟩⟩
    exact (hker (x⁻¹ * y.1)).mp (by rw [map_mul, map_inv, y.2, inv_mul_cancel])
  · intro z
    refine ⟨x * ⟨(z : G), z.2.1⟩, ?_⟩
    rw [map_mul, (hker ⟨(z : G), z.2.1⟩).mpr z.2.2, mul_one]
  · intro y
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  · intro z
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

theorem twistFibreFixedPoint (p k r : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    [DecidableEq (GaloisField p k)] (hrp : r.Prime) (hro : Odd r) (hrne : r ≠ p)
    (Q : Subgroup (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))))
    (hQ : Q ≤ Work.AUTL2.pgammaL (GaloisField p k))
    (hL : Work.AUTL2.pslImage (GaloisField p k) ≤ Q)
    (t : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) (htQ : t ∈ Q)
    (htinf : t OnePoint.infty = OnePoint.infty)
    (N : Subgroup (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))))
    (hNle : N ≤ Q)
    (hNcent : N ≤ Subgroup.centralizer ({t} : Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))))
    (hNnorm : ∀ c : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)),
        c ∈ Subgroup.centralizer ({t} : Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) → c ∈ Q →
        ∀ x ∈ N, c * x * c⁻¹ ∈ N)
    (hNr : IsPGroup r N) (x : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) (hxN : x ∈ N)
    (hxnpgl : x ∉ Work.AUTL2.pglImage (GaloisField p k)) :
    ∃ y ∈ N, y ∉ Work.AUTL2.pglImage (GaloisField p k) ∧
      ∀ c : GaloisField p k, Work.AUTL2.transl (GaloisField p k) c * t = t * Work.AUTL2.transl (GaloisField p k) c →
        y * Work.AUTL2.transl (GaloisField p k) c = Work.AUTL2.transl (GaloisField p k) c * y := by
  haveI hFin : Fintype (GaloisField p k) := Fintype.ofFinite _
  -- the Galois part of an element of `N`, as a homomorphism on `N`
  let incl : ↥N →* ↥(pgammaL (GaloisField p k)) :=
    MonoidHom.codRestrict (Q.subtype.comp (Subgroup.inclusion hNle))
      (pgammaL (GaloisField p k)) (fun y => hQ (hNle y.2))
  let ψ : ↥N →* (GaloisField p k ≃+* GaloisField p k) :=
    (SplitAux.galMap (GaloisField p k)).comp incl
  have hψ_iff : ∀ y : ↥N, ψ y = 1 ↔ (y : Equiv.Perm (P1 (GaloisField p k)))
      ∈ pglImage (GaloisField p k) := by
    intro y
    have h1 : ψ y = SplitAux.galPart (GaloisField p k) (incl y) := rfl
    rw [h1, SplitAux.galPart_eq_one_iff]
    rfl
  let xN : ↥N := ⟨x, hxN⟩
  have hγne : ψ xN ≠ 1 := fun h => hxnpgl ((hψ_iff xN).mp h)
  -- `K = N ∩ PGL(2,q)` has order coprime to `p`
  let K : Subgroup (Equiv.Perm (P1 (GaloisField p k))) :=
    N ⊓ pglImage (GaloisField p k)
  have hpK : ¬ p ∣ Nat.card ↥K := by
    haveI : Fact r.Prime := ⟨hrp⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := r) (G := ↥N)).mp hNr
    have hdvd : Nat.card ↥K ∣ r ^ n := by
      rw [← hn]
      exact Subgroup.card_dvd_of_le (show K ≤ N from inf_le_left)
    intro hpdvd
    have : p ∣ r ^ n := hpdvd.trans hdvd
    have heq : p = r :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hrp).mp
        ((Fact.out : p.Prime).dvd_of_dvd_pow (n := n) this)
    exact hrne heq.symm
  -- the `p`-group `V` of translations centralising `t`
  let V : Subgroup (Equiv.Perm (P1 (GaloisField p k))) :=
    Normalizer.translSub (GaloisField p k) ⊓
      Subgroup.centralizer ({t} : Set (Equiv.Perm (P1 (GaloisField p k))))
  have hVp : IsPGroup p ↥V := isPGroup_translCent (p := p) (k := k) t
  have hVleQ : V ≤ Q := fun v hv => hL (Normalizer.translSub_le_pslImage _ hv.1)
  have hVcent : V ≤ Subgroup.centralizer ({t} : Set (Equiv.Perm (P1 (GaloisField p k)))) :=
    fun v hv => hv.2
  have hVgal : ∀ v : ↥V, SplitAux.galPart (GaloisField p k)
      ⟨(v : Equiv.Perm (P1 (GaloisField p k))), hQ (hVleQ v.2)⟩ = 1 := fun v =>
    (SplitAux.galPart_eq_one_iff _ _).mpr
      (pslImage_le_pglImage _ (Normalizer.translSub_le_pslImage _ v.2.1))
  -- conjugation by `V` preserves `N` ...
  have hNconj : ∀ (v : ↥V) (w : ↥N),
      (v : Equiv.Perm (P1 (GaloisField p k))) * (w : Equiv.Perm (P1 (GaloisField p k)))
        * (v : Equiv.Perm (P1 (GaloisField p k)))⁻¹ ∈ N :=
    fun v w => hNnorm _ (hVcent v.2) (hVleQ v.2) _ w.2
  -- ... and does not change the Galois part
  have hψconj : ∀ (v : ↥V) (w : ↥N),
      ψ ⟨(v : Equiv.Perm (P1 (GaloisField p k))) * (w : Equiv.Perm (P1 (GaloisField p k)))
        * (v : Equiv.Perm (P1 (GaloisField p k)))⁻¹, hNconj v w⟩ = ψ w := by
    intro v w
    have h2 : ψ ⟨(v : Equiv.Perm (P1 (GaloisField p k))) * (w : Equiv.Perm (P1 (GaloisField p k)))
        * (v : Equiv.Perm (P1 (GaloisField p k)))⁻¹, hNconj v w⟩
        = SplitAux.galPart (GaloisField p k)
          ⟨(v : Equiv.Perm (P1 (GaloisField p k))) * (w : Equiv.Perm (P1 (GaloisField p k)))
            * (v : Equiv.Perm (P1 (GaloisField p k)))⁻¹, hQ (hNle (hNconj v w))⟩ := rfl
    have h1 : (⟨(v : Equiv.Perm (P1 (GaloisField p k))) * (w : Equiv.Perm (P1 (GaloisField p k)))
          * (v : Equiv.Perm (P1 (GaloisField p k)))⁻¹, hQ (hNle (hNconj v w))⟩ :
            ↥(pgammaL (GaloisField p k)))
        = ⟨(v : Equiv.Perm (P1 (GaloisField p k))), hQ (hVleQ v.2)⟩
          * ⟨(w : Equiv.Perm (P1 (GaloisField p k))), hQ (hNle w.2)⟩
          * ⟨(v : Equiv.Perm (P1 (GaloisField p k))), hQ (hVleQ v.2)⟩⁻¹ := by
      ext
      simp
    have h3 : SplitAux.galPart (GaloisField p k)
        ⟨(v : Equiv.Perm (P1 (GaloisField p k))) * (w : Equiv.Perm (P1 (GaloisField p k)))
          * (v : Equiv.Perm (P1 (GaloisField p k)))⁻¹, hQ (hNle (hNconj v w))⟩
        = SplitAux.galPart (GaloisField p k)
            ⟨(v : Equiv.Perm (P1 (GaloisField p k))), hQ (hVleQ v.2)⟩
          * SplitAux.galPart (GaloisField p k)
            ⟨(w : Equiv.Perm (P1 (GaloisField p k))), hQ (hNle w.2)⟩
          * (SplitAux.galPart (GaloisField p k)
            ⟨(v : Equiv.Perm (P1 (GaloisField p k))), hQ (hVleQ v.2)⟩)⁻¹ := by
      rw [h1, ← SplitAux.galMap_apply, map_mul, map_mul, map_inv]
      rfl
    rw [h2, h3, hVgal v, one_mul, inv_one, mul_one]
    rfl
  -- the `V`-set: the fibre of `ψ` through `x`, of cardinality `|K|`
  let Ω : Type _ := {y : ↥N // ψ y = ψ xN}
  have hcardΩ : Nat.card Ω = Nat.card ↥K :=
    card_fibre_eq_card_inf_ker N (pglImage (GaloisField p k)) ψ hψ_iff xN
  letI : MulAction ↥V Ω :=
    { smul := fun v y =>
        ⟨⟨(v : Equiv.Perm (P1 (GaloisField p k)))
            * (y.1 : Equiv.Perm (P1 (GaloisField p k)))
            * (v : Equiv.Perm (P1 (GaloisField p k)))⁻¹, hNconj v y.1⟩, by
          show ψ ⟨(v : Equiv.Perm (P1 (GaloisField p k)))
              * (y.1 : Equiv.Perm (P1 (GaloisField p k)))
              * (v : Equiv.Perm (P1 (GaloisField p k)))⁻¹, hNconj v y.1⟩ = ψ xN
          rw [hψconj v y.1]
          exact y.2⟩
      one_smul := by
        intro y
        apply Subtype.ext
        apply Subtype.ext
        change (1 : Equiv.Perm (P1 (GaloisField p k)))
            * ((y.1 : ↥N) : Equiv.Perm (P1 (GaloisField p k)))
            * (1 : Equiv.Perm (P1 (GaloisField p k)))⁻¹
          = ((y.1 : ↥N) : Equiv.Perm (P1 (GaloisField p k)))
        group
      mul_smul := by
        intro v w y
        apply Subtype.ext
        apply Subtype.ext
        change ((v * w : ↥V) : Equiv.Perm (P1 (GaloisField p k)))
            * ((y.1 : ↥N) : Equiv.Perm (P1 (GaloisField p k)))
            * ((v * w : ↥V) : Equiv.Perm (P1 (GaloisField p k)))⁻¹
          = ((v : ↥V) : Equiv.Perm (P1 (GaloisField p k)))
            * (((w : ↥V) : Equiv.Perm (P1 (GaloisField p k)))
              * ((y.1 : ↥N) : Equiv.Perm (P1 (GaloisField p k)))
              * ((w : ↥V) : Equiv.Perm (P1 (GaloisField p k)))⁻¹)
            * ((v : ↥V) : Equiv.Perm (P1 (GaloisField p k)))⁻¹
        rw [Subgroup.coe_mul]
        group }
  obtain ⟨y, hy⟩ := hVp.nonempty_fixed_point_of_prime_not_dvd_card Ω (by rw [hcardΩ]; exact hpK)
  -- `y` is centralised by every element of `V`
  have hyfix : ∀ v : ↥V, (v : Equiv.Perm (P1 (GaloisField p k)))
      * ((y.1 : ↥N) : Equiv.Perm (P1 (GaloisField p k)))
      * (v : Equiv.Perm (P1 (GaloisField p k)))⁻¹
      = ((y.1 : ↥N) : Equiv.Perm (P1 (GaloisField p k))) := fun v => by
    have h : v • y = y := MulAction.mem_fixedPoints.mp hy v
    have h1 : ((v • y).1 : Equiv.Perm (P1 (GaloisField p k)))
        = ((y.1 : ↥N) : Equiv.Perm (P1 (GaloisField p k))) :=
      congrArg (fun w : ↥N => ((w : Equiv.Perm (P1 (GaloisField p k)))))
        (congrArg Subtype.val h)
    exact h1
  refine ⟨((y.1 : ↥N) : Equiv.Perm (P1 (GaloisField p k))), y.1.2, ?_, ?_⟩
  · intro hypgl
    exact hγne (by rw [← y.2, (hψ_iff y.1).mpr hypgl])
  · intro c hc
    have hv : transl (GaloisField p k) c ∈ V :=
      ⟨Normalizer.transl_mem_translSub _ c, Subgroup.mem_centralizer_singleton_iff.mpr hc⟩
    have h1 : transl (GaloisField p k) c
        * ((y.1 : ↥N) : Equiv.Perm (P1 (GaloisField p k)))
        * (transl (GaloisField p k) c)⁻¹
        = ((y.1 : ↥N) : Equiv.Perm (P1 (GaloisField p k))) :=
      hyfix ⟨transl (GaloisField p k) c, hv⟩
    have h2 : transl (GaloisField p k) c
        * ((y.1 : ↥N) : Equiv.Perm (P1 (GaloisField p k)))
        = ((y.1 : ↥N) : Equiv.Perm (P1 (GaloisField p k)))
          * transl (GaloisField p k) c := by
      calc transl (GaloisField p k) c
            * ((y.1 : ↥N) : Equiv.Perm (P1 (GaloisField p k)))
          = (transl (GaloisField p k) c)
              * ((y.1 : ↥N) : Equiv.Perm (P1 (GaloisField p k)))
              * (transl (GaloisField p k) c)⁻¹ * transl (GaloisField p k) c := by group
        _ = ((y.1 : ↥N) : Equiv.Perm (P1 (GaloisField p k)))
              * transl (GaloisField p k) c := by rw [h1]
    exact h2.symm

end Work.DSTR.M110
