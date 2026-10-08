import Mathlib
import Submission.Work.DSTR.M110.twistBasics
import Submission.Work.DSTR.M110.Stabilizer
import Submission.Work.DSTR.M110.twistOuterInvolutionFixedPoint
import Submission.Work.DSTR.M110.twistTranslCentralizer
import Submission.Work.DSTR.M110.twistOddCore2
import Submission.Work.DSTR.M110.twistFibreFixedPoint

/-!
# Twist case of DS10a (`D110iiModelProp`)

`Work.DSTR.M110.twistCaseProof` : for `t in Q <= PΓL(2,q)` an involution with `t notin PGL(2,q)` and
an odd `r`-group `N <= C_Q(t)` normalized by `C_Q(t)`, one has `N <= PSL(2,q)`.

The proof conjugates the configuration (using that a twist involution has a fixed point on `P¹`, so
that it may be assumed to fix `∞`).  Then either

* `r = p`: `N` is an odd-order normal subgroup of the centralizer `C_Q(t)`, and `twistOddCore2`
  applies; or
* `r ≠ p`: the `p`-group `V` of translations centralizing `t` acts on the fibre of the Galois-part
  map through `x ∈ N`, so (`twistFibreFixedPoint`) there is `y ∈ N ∖ PGL(2,q)` commuting with all
  translations commuting with `t`; `twistTranslCentralizer` (an "odd order plus unipotent" argument)
  forces `y ∈ PGL(2,q)`, a contradiction.
-/

namespace Work.DSTR.M110

open Work.AUTL2

/-- **The twist case with `t` fixing `∞`.** -/
lemma twistCase_of_fixes_infty (p k r : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    [DecidableEq (GaloisField p k)] (hrp : r.Prime) (hro : Odd r)
    (Q : Subgroup (Equiv.Perm (P1 (GaloisField p k))))
    (hL : pslImage (GaloisField p k) ≤ Q)
    (hQ : Q ≤ pgammaL (GaloisField p k))
    (t : Equiv.Perm (P1 (GaloisField p k)))
    (htQ : t ∈ Q) (htinf : t OnePoint.infty = OnePoint.infty)
    (ht2 : orderOf t = 2) (htnpgl : t ∉ pglImage (GaloisField p k))
    (N : Subgroup (Equiv.Perm (P1 (GaloisField p k))))
    (hNle : N ≤ Q)
    (hNcent : N ≤ Subgroup.centralizer ({t} : Set (Equiv.Perm (P1 (GaloisField p k)))))
    (hNnorm : ∀ c : Equiv.Perm (P1 (GaloisField p k)),
        c ∈ Subgroup.centralizer ({t} : Set (Equiv.Perm (P1 (GaloisField p k)))) → c ∈ Q →
        ∀ x ∈ N, c * x * c⁻¹ ∈ N)
    (hNr : IsPGroup r N) :
    N ≤ pslImage (GaloisField p k) := by
  by_cases hcase : r = p
  · -- `r = p`: `N` is an odd-order normal subgroup of the centralizer `Q ⊓ C(t)`
    have hNr' : IsPGroup p N := hcase ▸ hNr
    haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
    have hNodd : Odd (Nat.card ↥N) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := ↥N)).mp hNr'
      rw [hn]
      exact hp.pow
    exact twistOddCore2 p k hp hq t (hQ htQ) ht2 htnpgl
      (Q ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (P1 (GaloisField p k)))))
      (fun x hx => hQ hx.1) (fun x hx => hx.2) (fun x hx => ⟨hL hx.1, hx.2⟩) N
      (fun x hx => ⟨hNle hx, hNcent hx⟩) (fun c hc => hNnorm c hc.2 hc.1) hNodd
  · -- `r ≠ p`: a `V`-fixed element of the fibre is an odd-order element commuting with `V`
    have hNpgl : N ≤ pglImage (GaloisField p k) := by
      intro x hxN
      by_contra hxnpgl
      obtain ⟨y, hyN, hynpgl, hycomm⟩ :=
        twistFibreFixedPoint p k r hp hq hrp hro hcase Q hQ hL t htQ htinf N hNle hNcent hNnorm
          hNr x hxN hxnpgl
      exact hynpgl
        (twistTranslCentralizer p k hp hq t y (hQ htQ) htinf ht2 htnpgl (hQ (hNle hyN))
          (odd_orderOf_of_mem_isPGroup r hro N hNr hyN) hycomm)
    intro x hxN
    exact mem_pslImage_of_odd_of_mem_pglImage (p := p) (k := k) x (hNpgl hxN)
      (odd_orderOf_of_mem_isPGroup r hro N hNr hxN)

theorem twistCaseProof (p k r : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    [DecidableEq (GaloisField p k)] (hrp : r.Prime) (hro : Odd r)
    (Q : Subgroup (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))))
    (hL : Work.AUTL2.pslImage (GaloisField p k) ≤ Q)
    (hQ : Q ≤ Work.AUTL2.pgammaL (GaloisField p k))
    (t : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))
    (htQ : t ∈ Q) (ht2 : orderOf t = 2) (htnpgl : t ∉ Work.AUTL2.pglImage (GaloisField p k))
    (N : Subgroup (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))))
    (hNle : N ≤ Q)
    (hNcent : N ≤ Subgroup.centralizer ({t} : Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))))
    (hNnorm : ∀ c : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)),
        c ∈ Subgroup.centralizer ({t} : Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) → c ∈ Q →
        ∀ x ∈ N, c * x * c⁻¹ ∈ N)
    (hNr : IsPGroup r N) :
    N ≤ Work.AUTL2.pslImage (GaloisField p k) := by
  -- `t` has a fixed point; conjugate the whole configuration so that `t` fixes `∞`
  obtain ⟨p₀, hp₀⟩ := twistOuterInvolutionFixedPoint p k hp hq t (hQ htQ) ht2 htnpgl
  obtain ⟨g, hgS, hgp₀⟩ := exists_pslImage_map_to_infty (F := GaloisField p k) p₀
  have hgG : g ∈ pgammaL (GaloisField p k) :=
    Subgroup.mem_sup_left (pslImage_le_pglImage (GaloisField p k) hgS)
  have hginvS : g⁻¹ ∈ pslImage (GaloisField p k) := Subgroup.inv_mem _ hgS
  have hginvG : g⁻¹ ∈ pgammaL (GaloisField p k) :=
    Subgroup.mem_sup_left (pslImage_le_pglImage (GaloisField p k) hginvS)
  have hginv_infty : g⁻¹ OnePoint.infty = p₀ := by
    have h : g⁻¹ (g p₀) = g⁻¹ OnePoint.infty := congrArg (fun z => g⁻¹ z) hgp₀
    rw [← Equiv.Perm.mul_apply, inv_mul_cancel] at h
    simpa using h.symm
  -- the conjugating homomorphism `z ↦ g * z * g⁻¹`
  let cj : Equiv.Perm (P1 (GaloisField p k)) →* Equiv.Perm (P1 (GaloisField p k)) :=
    { toFun := fun z => g * z * g⁻¹
      map_one' := by group
      map_mul' := fun a b => by group }
  have hcj : ∀ z : Equiv.Perm (P1 (GaloisField p k)), cj z = g * z * g⁻¹ := fun z => rfl
  have hcj_inj : Function.Injective cj := by
    intro a b hab
    have h := hab
    rw [hcj a, hcj b] at h
    have h' := congrArg (fun z => g⁻¹ * z * g) h
    have e1 : g⁻¹ * (g * a * g⁻¹) * g = a := by group
    have e2 : g⁻¹ * (g * b * g⁻¹) * g = b := by group
    rwa [e1, e2] at h'
  -- the conjugated data
  let Q' : Subgroup (Equiv.Perm (P1 (GaloisField p k))) := Subgroup.map cj Q
  let N' : Subgroup (Equiv.Perm (P1 (GaloisField p k))) := Subgroup.map cj N
  let t' : Equiv.Perm (P1 (GaloisField p k)) := cj t
  have ht'inf : t' OnePoint.infty = OnePoint.infty := by
    rw [show t' = g * t * g⁻¹ from hcj t]
    simp only [Equiv.Perm.mul_apply, hginv_infty, hp₀, hgp₀]
  have ht'2 : orderOf t' = 2 := by
    have htt : t * t = 1 := by
      have h := pow_orderOf_eq_one t
      rwa [ht2, pow_two] at h
    have hsq : t' * t' = 1 := by
      rw [show t' = g * t * g⁻¹ from hcj t,
        show (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ from by group, htt]
      group
    refine orderOf_eq_prime (p := 2) hsq ?_
    intro h1
    have ht1 : t = 1 := by
      have h2 : g * t * g⁻¹ = 1 := by rw [← hcj t]; exact h1
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [h2]; group
    rw [ht1, orderOf_one] at ht2
    omega
  have ht'n : t' ∉ pglImage (GaloisField p k) := by
    intro hmem
    have h1 : g⁻¹ * t' * g ∈ pglImage (GaloisField p k) :=
      conj_mem_pglImage (y := t') hginvG hmem
    have h2 : g⁻¹ * t' * g = t := by
      rw [show t' = g * t * g⁻¹ from hcj t]
      group
    exact htnpgl (h2 ▸ h1)
  have hL' : pslImage (GaloisField p k) ≤ Q' := by
    intro x hxS
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have hm : g⁻¹ * x * g ∈ pslImage (GaloisField p k) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgS) hxS) hgS
      exact hL hm
    · show cj (g⁻¹ * x * g) = x
      rw [hcj]
      group
  have hQ' : Q' ≤ pgammaL (GaloisField p k) := by
    rintro x ⟨y, hyQ, rfl⟩
    rw [hcj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgG (hQ hyQ)) (Subgroup.inv_mem _ hgG)
  have ht'Q' : t' ∈ Q' := Subgroup.mem_map.mpr ⟨t, htQ, rfl⟩
  have hN'le : N' ≤ Q' := Subgroup.map_mono hNle
  have hN'cent : N' ≤ Subgroup.centralizer ({t'} : Set (Equiv.Perm (P1 (GaloisField p k)))) := by
    rintro y ⟨x, hxN, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show cj x * cj t = cj t * cj x
    rw [← map_mul, ← map_mul]
    exact congrArg cj (Subgroup.mem_centralizer_singleton_iff.mp (hNcent hxN))
  have hN'norm : ∀ c : Equiv.Perm (P1 (GaloisField p k)),
      c ∈ Subgroup.centralizer ({t'} : Set (Equiv.Perm (P1 (GaloisField p k)))) → c ∈ Q' →
      ∀ x ∈ N', c * x * c⁻¹ ∈ N' := by
    rintro c hccent hcQ x hxN
    obtain ⟨c₀, hc₀Q, rfl⟩ := Subgroup.mem_map.mp hcQ
    obtain ⟨x₀, hx₀N, rfl⟩ := Subgroup.mem_map.mp hxN
    have hc₀cent : c₀ ∈ Subgroup.centralizer ({t} : Set (Equiv.Perm (P1 (GaloisField p k)))) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hccent
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hcj_inj
      rw [map_mul, map_mul]
      exact hccent
    refine Subgroup.mem_map.mpr ⟨c₀ * x₀ * c₀⁻¹, hNnorm c₀ hc₀cent hc₀Q x₀ hx₀N, ?_⟩
    show cj (c₀ * x₀ * c₀⁻¹) = cj c₀ * cj x₀ * (cj c₀)⁻¹
    rw [map_mul, map_mul, map_inv]
  have hN'r : IsPGroup r N' := hNr.map cj
  have hres : N' ≤ pslImage (GaloisField p k) :=
    twistCase_of_fixes_infty p k r hp hq hrp hro Q' hL' hQ' t' ht'Q' ht'inf ht'2 ht'n
      N' hN'le hN'cent hN'norm hN'r
  intro x hxN
  have hmem : cj x ∈ N' := Subgroup.mem_map.mpr ⟨x, hxN, rfl⟩
  have hxS : cj x ∈ pslImage (GaloisField p k) := hres hmem
  have hxeq : x = g⁻¹ * cj x * g := by rw [hcj x]; group
  rw [hxeq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hginvS hxS) hgS

end Work.DSTR.M110
