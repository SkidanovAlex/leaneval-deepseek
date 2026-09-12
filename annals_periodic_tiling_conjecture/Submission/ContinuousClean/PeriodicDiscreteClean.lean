import Mathlib
import ChallengeDeps
import Submission.Commons.Algebra.Module.ZLattice.finiteIndex_comap_of_range_le

open Filter Bornology MeasureTheory
open scoped Pointwise

namespace Submission.ContinuousClean

open PeriodicTilingConjecture

def intCastLin {d : ℕ} : (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℝ) :=
  (Int.castAddHom ℝ).toIntLinearMap.compLeft (Fin d)

@[simp] lemma intCastLin_apply {d : ℕ} (z : Fin d → ℤ) :
    intCastLin (d:=d) z = fun i : Fin d => (z i : ℝ) := by
  ext i
  simp [intCastLin]

lemma intCastLin_range_eq_latticeSet {d : ℕ} :
    LinearMap.range (intCastLin (d:=d)) =
      {x : Fin d → ℝ | ∃ z : Fin d → ℤ, ∀ i : Fin d, x i = (z i : ℝ)} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, fun i => by simp⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    ext i
    simpa using (hz i).symm

lemma range_intCastLin_of_eq {d : ℕ} {F : Set (Fin d → ℤ)}
    {Λ : Set (Fin d → ℝ)} {s : Finset (Fin d → ℝ)} {L : Submodule ℤ (Fin d → ℝ)}
    (hΛs : Λ = s + L) {t : Fin d → ℝ}
    (hEq : Λ + (fun z : Fin d → ℤ => fun i : Fin d => (z i : ℝ)) '' F =
      (fun x : Fin d → ℝ => x + t) ''
        {x : Fin d → ℝ | ∃ z : Fin d → ℤ, ∀ i : Fin d, x i = (z i : ℝ)}) :
    L ≤ LinearMap.range (intCastLin (d:=d)) := by
  intro x hx
  let e := intCastLin (d:=d)
  let latticeSet : Set (Fin d → ℝ) := {x | ∃ z : Fin d → ℤ, ∀ i : Fin d, x i = (z i : ℝ)}
  have hlat : LinearMap.range e = latticeSet := by
    simpa [e, latticeSet] using intCastLin_range_eq_latticeSet (d:=d)
  have hRne : ((fun x : Fin d → ℝ => x + t) '' latticeSet).Nonempty := by
    refine ⟨e 0 + t, ?_⟩
    refine ⟨e 0, ?_, rfl⟩
    rw [← hlat]
    exact ⟨0, rfl⟩
  have hEq' : Λ + e '' F = (fun x => x + t) '' latticeSet := by
    simpa [e, latticeSet] using hEq
  have hLne : (Λ + e '' F).Nonempty := by
    rwa [hEq']
  rcases hLne with ⟨y, hy⟩
  rw [Set.mem_add] at hy
  rcases hy with ⟨lam, hlam, yf, hyf, hsum_y⟩
  rw [Set.mem_image] at hyf
  rcases hyf with ⟨f, hf, rfl⟩
  have hlam_mem_add : lam ∈ (s : Set (Fin d → ℝ)) + (L : Set (Fin d → ℝ)) := by
    simpa [hΛs] using hlam
  rw [Set.mem_add] at hlam_mem_add
  rcases hlam_mem_add with ⟨a, ha, l, hl, hlamsum⟩
  have hbase_lhs : a + e f ∈ Λ + e '' F := by
    rw [Set.mem_add]
    refine ⟨a, ?_, e f, ?_, rfl⟩
    · rw [hΛs]
      rw [Set.mem_add]
      exact ⟨a, by simpa using ha, 0, L.zero_mem, by simp⟩
    · exact ⟨f, hf, rfl⟩
  have hbase_rhs : a + e f ∈ (fun x => x + t) '' latticeSet := by
    have htmp := hbase_lhs
    rwa [hEq'] at htmp
  rw [Set.mem_image] at hbase_rhs
  rcases hbase_rhs with ⟨y0, hy0, hy0eq⟩
  rw [← hlat] at hy0
  rcases hy0 with ⟨z0, rfl⟩
  have hx_lhs : a + x + e f ∈ Λ + e '' F := by
    rw [Set.mem_add]
    refine ⟨a + x, ?_, e f, ?_, rfl⟩
    · rw [hΛs]
      rw [Set.mem_add]
      exact ⟨a, by simpa using ha, x, hx, rfl⟩
    · exact ⟨f, hf, rfl⟩
  have hx_rhs : a + x + e f ∈ (fun x => x + t) '' latticeSet := by
    have htmp := hx_lhs
    rwa [hEq'] at htmp
  rw [Set.mem_image] at hx_rhs
  rcases hx_rhs with ⟨y1, hy1, hy1eq⟩
  rw [← hlat] at hy1
  rcases hy1 with ⟨z1, rfl⟩
  refine ⟨z1 - z0, ?_⟩
  have hz1 : e z1 + t = a + x + e f := hy1eq
  have hz0 : e z0 + t = a + e f := hy0eq
  calc
    e (z1 - z0) = e z1 - e z0 := by simp
    _ = x := by
      have h1 : e z1 = a + x + e f - t := by
        rw [← hz1]
        abel
      have h0 : e z0 = a + e f - t := by
        rw [← hz0]
        abel
      rw [h1, h0]
      abel

lemma exists_finset_eq_add_of_invariant {G : Type*} [AddCommGroup G] (H : AddSubgroup G) [H.FiniteIndex]
    {A : Set G} (hA : ∀ ⦃x⦄, x ∈ A → ∀ ⦃h⦄, h ∈ H → x + h ∈ A) :
    ∃ s : Finset G, A = s + H := by
  classical
  obtain ⟨S, hcompl, h0⟩ := AddSubgroup.exists_isComplement_left H 0
  have hSfin : S.Finite := AddSubgroup.IsComplement.finite_left hcompl
  let s : Finset G := hSfin.toFinset.filter (fun g => g ∈ A)
  refine ⟨s, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, huniq⟩ := hcompl.existsUnique x
    rcases p with ⟨⟨u, huS⟩, ⟨h, hhH⟩⟩
    have huA : u ∈ A := by
      have hneg : -h ∈ H := H.neg_mem hhH
      have hx' := hA hx hneg
      convert hx' using 1
      simpa [add_assoc] using (congrArg (fun y => y + -h) hp)
    have hu_mem_s : u ∈ s := by
      dsimp [s]
      rw [Finset.mem_filter]
      exact ⟨hSfin.mem_toFinset.mpr huS, huA⟩
    refine Set.mem_add.mpr ⟨u, hu_mem_s, h, hhH, ?_⟩
    simpa using hp
  · intro hx
    rw [Set.mem_add] at hx
    rcases hx with ⟨u, hu, h, hh, hux⟩
    have huA : u ∈ A := by
      dsimp [s] at hu
      exact (Finset.mem_filter.mp hu).2
    have hux' : u + h = x := hux
    exact hux' ▸ hA huA hh

lemma invariant_preimage {d : ℕ} {Λ : Set (Fin d → ℝ)} {s : Finset (Fin d → ℝ)}
    {L : Submodule ℤ (Fin d → ℝ)} (hΛs : Λ = (s : Set (Fin d → ℝ)) + L)
    {t : Fin d → ℝ} :
    ∀ x ∈ ({z : Fin d → ℤ | intCastLin (d:=d) z ∈ Λ - ({t} : Set (Fin d → ℝ))}),
      ∀ h ∈ ((L.comap (intCastLin (d:=d))).toAddSubgroup),
        x + h ∈ ({z : Fin d → ℤ | intCastLin (d:=d) z ∈ Λ - ({t} : Set (Fin d → ℝ))}) := by
  intro x hx h hH
  let e := intCastLin (d:=d)
  let H : AddSubgroup (Fin d → ℤ) := (L.comap e).toAddSubgroup
  have hxset : e x ∈ Λ - ({t} : Set (Fin d → ℝ)) := by
    simpa [e] using hx
  rw [Set.mem_sub] at hxset
  rcases hxset with ⟨lam, hlam, u, hu, hxeq⟩
  have hu_t : u = t := by simpa using hu
  subst u
  have heh : e h ∈ L := by
    have hh : h ∈ L.comap e := by
      simpa [H, e] using hH
    exact (Submodule.mem_comap.mp hh)
  have hlam_add : lam + e h ∈ Λ := by
    have hΛs' : Λ = (s : Set (Fin d → ℝ)) + (L : Set (Fin d → ℝ)) := by
      simpa using hΛs
    rw [hΛs'] at hlam ⊢
    rw [Set.mem_add] at hlam ⊢
    rcases hlam with ⟨a, ha, v, hv, rfl⟩
    refine ⟨a, ha, v + e h, L.add_mem hv heh, ?_⟩
    abel
  change e (x + h) ∈ Λ - ({t} : Set (Fin d → ℝ))
  rw [Set.mem_sub]
  refine ⟨lam + e h, hlam_add, t, by simp, ?_⟩
  calc
    (lam + e h) - t = (lam - t) + e h := by abel
    _ = e x + e h := by simp [← hxeq]
    _ = e (x + h) := by exact (e.map_add x h).symm

theorem periodic_discrete_clean
    {d : ℕ} {F : Set (Fin d → ℤ)} (hFne : F.Nonempty)
    {Λ : Set (Fin d → ℝ)} (hΛ : IsPeriodicContinuousTilingSet Λ)
    {t : Fin d → ℝ}
    (hEq : Λ + (fun z : Fin d → ℤ => fun i : Fin d => (z i : ℝ)) '' F =
      (fun x : Fin d → ℝ => x + t) ''
        {x : Fin d → ℝ | ∃ z : Fin d → ℤ, ∀ i : Fin d, x i = (z i : ℝ)}) :
    IsPeriodicTilingSet {z : Fin d → ℤ |
      (fun i : Fin d => (z i : ℝ)) ∈ Λ - ({t} : Set (Fin d → ℝ))} := by
  classical
  rcases hΛ with ⟨L, hLdisc, hLlat, s, hΛs⟩
  letI : DiscreteTopology L := hLdisc
  letI : IsZLattice ℝ L := hLlat
  let e := intCastLin (d:=d)
  let H : AddSubgroup (Fin d → ℤ) := (L.comap e).toAddSubgroup
  have he_inj : Function.Injective e := by
    intro z w h
    funext i
    have hi : (z i : ℝ) = (w i : ℝ) := by
      simpa [e] using congrFun h i
    exact_mod_cast hi
  have hLrange : L ≤ LinearMap.range e := by
    simpa [e] using range_intCastLin_of_eq (d:=d) (F:=F) (Λ:=Λ) (s:=s) (L:=L) hΛs hEq
  have hHfin : H.FiniteIndex := by
    exact Commons.Algebra.Module.ZLattice.finiteIndex_comap_of_range_le (e := e) he_inj hLrange
  have hA_inv : ∀ x ∈ ({z : Fin d → ℤ | (fun i : Fin d => (z i : ℝ)) ∈ Λ - ({t} : Set (Fin d → ℝ))}),
      ∀ h ∈ H, x + h ∈ ({z : Fin d → ℤ | (fun i : Fin d => (z i : ℝ)) ∈ Λ - ({t} : Set (Fin d → ℝ))}) := by
    intro x hx h hh
    have hΛs' : Λ = (s : Set (Fin d → ℝ)) + (L : Set (Fin d → ℝ)) := by
      simpa using hΛs
    have hx' : x ∈ ({z : Fin d → ℤ | intCastLin (d:=d) z ∈ Λ - ({t} : Set (Fin d → ℝ))}) := by
      simpa [e] using hx
    have hh' : h ∈ ((L.comap (intCastLin (d:=d))).toAddSubgroup) := by
      simpa [H, e] using hh
    have hsum := invariant_preimage hΛs' x hx' h hh'
    simpa [e] using hsum
  obtain ⟨s0, hs0⟩ := exists_finset_eq_add_of_invariant H hA_inv
  refine ⟨H, hHfin, s0, ?_⟩
  simpa [e] using hs0

end Submission.ContinuousClean
